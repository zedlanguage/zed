//! Deep programs, such as a generator writes: the parser, the syntax tree and the formatter hold
//! their work on the heap, so a nest of any depth runs on a test thread's 2 MiB stack. Nothing
//! here asks for a larger stack, and the old recursive code overflows on each form.

use std::collections::HashMap;
use std::sync::{Mutex, PoisonError};

use zed_tests::scaling::{check, check_order};
use zedc::ast::{Expr, build};
use zedc::format::format_source;
use zedc::lex::{Token, lex};
use zedc::parse::{TOP, Tree, parse};

/// How deep the forms below nest: far past what the 2 MiB stack held (200 parentheses).
const DEEP: usize = 4_000;

/// `open` `n` times, `middle`, then `close` `n` times.
fn nest(open: &str, middle: &str, close: &str, n: usize) -> String {
    open.repeat(n) + middle + &close.repeat(n)
}

fn parens(n: usize) -> String {
    nest("(", "1", ")", n)
}
fn sum(n: usize) -> String {
    nest("a + ", "b", "", n)
}
fn negations(n: usize) -> String {
    nest("!", "ok", "", n)
}
fn powers(n: usize) -> String {
    nest("2 ** ", "2", "", n)
}
fn lambdas(n: usize) -> String {
    nest("x -> ", "x", "", n)
}
fn calls(n: usize) -> String {
    nest("f(", "1", ")", n)
}
fn named_calls(n: usize) -> String {
    nest("f(x: ", "1", ")", n)
}
fn indexes(n: usize) -> String {
    nest("a[", "1", "]", n)
}
fn tuples(n: usize) -> String {
    nest("(1, ", "2", ")", n)
}
fn blocks(n: usize) -> String {
    nest("{ return ", "1", "; }", n)
}
fn else_ifs(n: usize) -> String {
    nest("if c { 1 } else ", "{ 2 }", "", n)
}
fn ifs_in_branches(n: usize) -> String {
    nest("if c { ", "1", " } else { 2 }", n)
}
fn defaults(n: usize) -> String {
    nest("a else (", "c", ")", n)
}
fn holes(n: usize) -> String {
    nest("\"${", "0", "}\"", n)
}
fn lambda_defaults(n: usize) -> String {
    nest("((x = ", "0", ") -> x)", n)
}
fn patterns(n: usize) -> String {
    format!("e else {} -> 0", nest("#a(", "#a", ")", n))
}
fn field_patterns(n: usize) -> String {
    format!("e else {} -> 0", nest("#a(f: ", "#a", ")", n))
}
fn grouped_types(n: usize) -> String {
    format!("x is {}", nest("(", "A", ")", n))
}
fn arrow_types(n: usize) -> String {
    format!("x is ({})", nest("A -> ", "B", "", n))
}
fn tuple_types(n: usize) -> String {
    format!("x is {}", nest("(A, ", "B", ")", n))
}
fn unions_in_groups(n: usize) -> String {
    format!("x is {}", nest("(A | ", "B", ")", n))
}
fn differences(n: usize) -> String {
    format!("x is {}", nest("A \\ ", "B", "", n))
}
fn long_union(n: usize) -> String {
    format!("x is {}", nest("A | ", "B", "", n))
}

/// All the steps from text to text.
fn every_stage(text: &str) {
    let tokens = lex(text).unwrap();
    let tree = parse(text, &tokens, "Expr", TOP).unwrap();
    let e = build(text, &tokens, &tree).unwrap();
    assert!(!e.to_string().is_empty());
    assert_eq!(format!("{e:?}"), e.to_string());
    let unit = format!("f(c) = {text};\n");
    let once = format_source(unit.as_bytes()).unwrap();
    assert_eq!(format_source(once.as_bytes()).unwrap(), once);
}

/// The syntax tree of `text`.
fn shown(text: &str) -> String {
    let tokens = lex(text).unwrap();
    let tree = parse(text, &tokens, "Expr", TOP).unwrap();
    build(text, &tokens, &tree).unwrap().to_string()
}

macro_rules! deep_forms {
    ($($deep:ident $scales:ident $form:ident $two:expr, $written:expr;)*) => {
        $(
            #[test]
            fn $deep() {
                assert_eq!(shown(&$form(2)), $two);
                let unit = format!("f(c) = {};\n", $form(2));
                assert_eq!(format_source(unit.as_bytes()).unwrap(), $written);
                every_stage(&$form(DEEP));
            }

            #[test]
            fn $scales() {
                every_stage_scales(stringify!($form), $form);
            }
        )*
    };
}

deep_forms! {
    deep_parentheses parentheses_scale parens "1", "f(c) = 1;\n";
    a_long_sum a_long_sum_scales sum "(+ (+ a a) b)", "f(c) = a + a + b;\n";
    deep_prefix_operators prefix_operators_scale negations "(! (! ok))", "f(c) = !(!ok);\n";
    deep_powers powers_scale powers "(** 2 (** 2 2))", "f(c) = 2 ** 2 ** 2;\n";
    deep_lambdas lambdas_scale lambdas "(fn (x) (fn (x) x))", "f(c) = x -> x -> x;\n";
    deep_calls calls_scale calls "(call f (call f 1))", "f(c) = f(f(1));\n";
    deep_named_arguments named_arguments_scale named_calls
        "(call f (x: (call f (x: 1))))", "f(c) = f(x: f(x: 1));\n";
    deep_indexes indexes_scale indexes "(index a (index a 1))", "f(c) = a[a[1]];\n";
    deep_tuples tuples_scale tuples "(tuple 1 (tuple 1 2))", "f(c) = (1, (1, 2));\n";
    deep_blocks blocks_scale blocks
        "(block (return (block (return 1))))", "f(c) = { return { return 1; }; };\n";
    a_long_else_if_chain else_if_chains_scale else_ifs
        "(if c (block (return 1)) (if c (block (return 1)) (block (return 2))))",
        "f(c) = if c { 1 } else if c { 1 } else { 2 };\n";
    deep_ifs_in_branches ifs_in_branches_scale ifs_in_branches
        "(if c (block (return (if c (block (return 1)) (block (return 2))))) (block (return 2)))",
        "f(c) = if c { if c { 1 } else { 2 } } else { 2 };\n";
    deep_else_defaults else_defaults_scale defaults
        "(else a (else a c))", "f(c) = a else (a else c);\n";
    deep_string_holes string_holes_scale holes
        "(str (str 0))", "f(c) = \"${\"${0}\"}\";\n";
    deep_parameter_defaults parameter_defaults_scale lambda_defaults
        "(fn ((x = (fn ((x = 0)) x))) x)", "f(c) = (x = (x = 0) -> x) -> x;\n";
    deep_patterns patterns_scale patterns "(else e #a(#a(#a)) 0)", "f(c) = e else #a(#a(#a)) -> 0;\n";
    deep_field_patterns field_patterns_scale field_patterns
        "(else e #a(f: #a(f: #a)) 0)", "f(c) = e else #a(f: #a(f: #a)) -> 0;\n";
    deep_grouped_types grouped_types_scale grouped_types "(is x A)", "f(c) = x is A;\n";
    deep_function_types function_types_scale arrow_types
        "(is x (-> (A) (-> (A) B)))", "f(c) = x is (A -> A -> B);\n";
    deep_tuple_types tuple_types_scale tuple_types
        "(is x (tuple A (tuple A B)))", "f(c) = x is (A, (A, B));\n";
    deep_unions deep_unions_scale unions_in_groups
        "(is x (| A (| A B)))", "f(c) = x is A | (A | B);\n";
    a_long_difference differences_scale differences
        "(is x (\\ (\\ A A) B))", "f(c) = x is A \\ A \\ B;\n";
    a_long_union long_unions_scale long_union
        "(is x (| A A B))", "f(c) = x is A | A | B;\n";
}

/// `form` at depths `n` and `8n`, lexed and parsed.
fn parsed(n: usize, form: fn(usize) -> String) -> HashMap<usize, (String, Vec<Token>, Tree)> {
    [n, 8 * n]
        .into_iter()
        .map(|m| {
            let text = form(m);
            let tokens = lex(&text).unwrap();
            let tree = parse(&text, &tokens, "Expr", TOP).unwrap();
            (m, (text, tokens, tree))
        })
        .collect()
}

/// One form is measured at a time: forms measured together compete for memory, which slows
/// the larger size more than the smaller.
static MEASURING: Mutex<()> = Mutex::new(());

/// Each stage of `form` at depths n and 8n, the inputs made before the clock starts.
fn every_stage_scales(what: &str, form: fn(usize) -> String) {
    const N: usize = 200;
    let inputs = parsed(N, form);
    let units: HashMap<usize, String> = inputs
        .iter()
        .map(|(&m, (text, ..))| (m, format!("f(c) = {text};\n")))
        .collect();
    let exprs: HashMap<usize, Expr> = inputs
        .iter()
        .map(|(&m, (text, tokens, tree))| (m, build(text, tokens, tree).unwrap()))
        .collect();
    let _alone = MEASURING.lock().unwrap_or_else(PoisonError::into_inner);
    check(&format!("lexing {what}"), N, |m| {
        lex(&inputs[&m].0).unwrap();
    });
    check(&format!("parsing {what}"), N, |m| {
        let (text, tokens, _) = &inputs[&m];
        parse(text, tokens, "Expr", TOP).unwrap();
    });
    check(&format!("formatting {what}"), N, |m| {
        format_source(units[&m].as_bytes()).unwrap();
    });
    check(&format!("building and dropping {what}"), N, |m| {
        let (text, tokens, tree) = &inputs[&m];
        build(text, tokens, tree).unwrap();
    });
    check(&format!("printing {what}"), N, |m| {
        exprs[&m].to_string();
    });
}

/// Blocks of two statements are written on lines of their own, each indented by its depth, so
/// the output itself has n² characters.
#[test]
fn deep_blocks_of_lines_are_written_at_the_order_of_their_text() {
    let unit = |n: usize| format!("f(c) = {};\n", nest("{ y = ", "1", "; y }", n));
    assert_eq!(
        format_source(unit(1).as_bytes()).unwrap(),
        "f(c) = {\n  y = 1;\n  y\n};\n"
    );
    let units: HashMap<usize, String> = [250, 2_000].into_iter().map(|m| (m, unit(m))).collect();
    check_order("nested blocks of two lines, by depth", 250, 2, |m| {
        let out = format_source(units[&m].as_bytes()).unwrap();
        assert!(out.len() > 2 * m * m);
    });
}

/// A form of a later layer at the bottom of a deep nest is reported, with its own place.
#[test]
fn an_error_at_the_bottom_of_a_deep_nest_is_reported() {
    let text = nest("(", "{ 1 }", ")", DEEP);
    let tokens = lex(&text).unwrap();
    let tree = parse(&text, &tokens, "Expr", TOP).unwrap();
    let e = build(&text, &tokens, &tree).unwrap_err();
    assert_eq!(e.span.start, DEEP);
    assert_eq!(e.message, "this form (Display) is built from layer L3");
}

/// The block at the bottom exports nothing; each block around it exports it.
#[test]
fn a_block_with_no_export_at_the_bottom_of_a_deep_nest_is_reported() {
    let text = nest("{ return ", "{ a = 1; }", "; }", DEEP);
    let tokens = lex(&text).unwrap();
    let tree = parse(&text, &tokens, "Expr", TOP).unwrap();
    let e = build(&text, &tokens, &tree).unwrap_err();
    assert_eq!(e.span.start, 9 * DEEP);
    assert!(e.message.starts_with("this block exports nothing"), "{e}");
}

#[test]
fn an_error_in_a_deep_string_hole_is_reported() {
    let text = nest("\"${", "{ 1 }", "}\"", DEEP);
    let tokens = lex(&text).unwrap();
    let tree = parse(&text, &tokens, "Expr", TOP).unwrap();
    let e = build(&text, &tokens, &tree).unwrap_err();
    assert_eq!(e.span.start, 3 * DEEP);
}

#[test]
fn a_missing_bracket_after_a_deep_nest_is_reported() {
    let text = "(".repeat(DEEP) + "1";
    let tokens = lex(&text).unwrap();
    let e = parse(&text, &tokens, "Expr", TOP).unwrap_err();
    assert_eq!(e.span.start, text.len());
}

/// A deep block and the holes in a string, in a unit of statements, with a comment kept at the
/// bottom, which forces a block of lines.
#[test]
fn a_comment_at_the_bottom_of_a_nest_of_blocks_is_kept() {
    let unit = format!("f(c) = {};\n", nest("{ return ", "// here\n1", "; }", 500));
    let out = format_source(unit.as_bytes()).unwrap();
    assert!(out.contains("// here\n"), "{}", &out[..200]);
    assert_eq!(format_source(out.as_bytes()).unwrap(), out);
}

/// No depth is too great: a nest of a hundred thousand parentheses is lexed, parsed, built, printed
/// and dropped on the test thread's stack.
#[test]
fn a_hundred_thousand_parentheses() {
    let text = parens(100_000);
    let tokens = lex(&text).unwrap();
    let tree = parse(&text, &tokens, "Expr", TOP).unwrap();
    let e = build(&text, &tokens, &tree).unwrap();
    assert_eq!(e.to_string(), "1");
}
