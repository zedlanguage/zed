//! Deep programs, such as a generator writes: the parser, the syntax tree and the formatter hold
//! their work on the heap, so a nest of any depth runs on a test thread's 2 MiB stack. Nothing
//! here asks for a larger stack, and the old recursive code overflows on each form.

use zedc::ast::build;
use zedc::format::format_source;
use zedc::lex::lex;
use zedc::parse::{TOP, parse};

/// How deep the forms below nest: far past what the 2 MiB stack held (200 parentheses).
const DEEP: usize = 4_000;

/// `open` `n` times, `middle`, then `close` `n` times.
fn nest(open: &str, middle: &str, close: &str, n: usize) -> String {
    open.repeat(n) + middle + &close.repeat(n)
}

pub(super) fn parens(n: usize) -> String {
    nest("(", "1", ")", n)
}
pub(super) fn sum(n: usize) -> String {
    nest("a + ", "b", "", n)
}
pub(super) fn negations(n: usize) -> String {
    nest("!", "ok", "", n)
}
pub(super) fn powers(n: usize) -> String {
    nest("2^", "2", "", n)
}
pub(super) fn lambdas(n: usize) -> String {
    nest("x -> ", "x", "", n)
}
pub(super) fn calls(n: usize) -> String {
    nest("f(", "1", ")", n)
}
pub(super) fn named_calls(n: usize) -> String {
    nest("f(x: ", "1", ")", n)
}
pub(super) fn indexes(n: usize) -> String {
    nest("a[", "1", "]", n)
}
pub(super) fn tuples(n: usize) -> String {
    nest("(1, ", "2", ")", n)
}
pub(super) fn blocks(n: usize) -> String {
    nest("{ return ", "1", "; }", n)
}
pub(super) fn else_ifs(n: usize) -> String {
    nest("if c { 1 } else ", "{ 2 }", "", n)
}
pub(super) fn ifs_in_branches(n: usize) -> String {
    nest("if c { ", "1", " } else { 2 }", n)
}
pub(super) fn defaults(n: usize) -> String {
    nest("a else (", "c", ")", n)
}
pub(super) fn holes(n: usize) -> String {
    nest("\"${", "0", "}\"", n)
}
pub(super) fn lambda_defaults(n: usize) -> String {
    nest("((x = ", "0", ") -> x)", n)
}
pub(super) fn patterns(n: usize) -> String {
    format!("e else {} -> 0", nest("#a(", "#a", ")", n))
}
pub(super) fn field_patterns(n: usize) -> String {
    format!("e else {} -> 0", nest("#a(f: ", "#a", ")", n))
}
pub(super) fn grouped_types(n: usize) -> String {
    format!("x is {}", nest("(", "A", ")", n))
}
pub(super) fn arrow_types(n: usize) -> String {
    format!("x is ({})", nest("A -> ", "B", "", n))
}
pub(super) fn tuple_types(n: usize) -> String {
    format!("x is {}", nest("(A, ", "B", ")", n))
}
pub(super) fn unions_in_groups(n: usize) -> String {
    format!("x is {}", nest("(A | ", "B", ")", n))
}
pub(super) fn differences(n: usize) -> String {
    format!("x is {}", nest("A \\ ", "B", "", n))
}
pub(super) fn long_union(n: usize) -> String {
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
    ($($deep:ident $form:ident $two:expr, $written:expr;)*) => {
        $(
            #[test]
            fn $deep() {
                assert_eq!(shown(&$form(2)), $two);
                let unit = format!("f(c) = {};\n", $form(2));
                assert_eq!(format_source(unit.as_bytes()).unwrap(), $written);
                every_stage(&$form(DEEP));
            }
        )*
    };
}

deep_forms! {
    deep_parentheses parens "1", "f(c) = 1;\n";
    a_long_sum sum "(+ (+ a a) b)", "f(c) = a + a + b;\n";
    deep_prefix_operators negations "(! (! ok))", "f(c) = !(!ok);\n";
    deep_powers powers "(^ 2 (^ 2 2))", "f(c) = 2^2^2;\n";
    deep_lambdas lambdas "(fn (x) (fn (x) x))", "f(c) = x -> x -> x;\n";
    deep_calls calls "(call f (call f 1))", "f(c) = f(f(1));\n";
    deep_named_arguments named_calls
        "(call f (x: (call f (x: 1))))", "f(c) = f(x: f(x: 1));\n";
    deep_indexes indexes "(index a (index a 1))", "f(c) = a[a[1]];\n";
    deep_tuples tuples "(tuple 1 (tuple 1 2))", "f(c) = (1, (1, 2));\n";
    deep_blocks blocks
        "(block (return (block (return 1))))", "f(c) = { return { return 1; }; };\n";
    a_long_else_if_chain else_ifs
        "(if c (block (return 1)) (if c (block (return 1)) (block (return 2))))",
        "f(c) = if c { 1 } else if c { 1 } else { 2 };\n";
    deep_ifs_in_branches ifs_in_branches
        "(if c (block (return (if c (block (return 1)) (block (return 2))))) (block (return 2)))",
        "f(c) = if c { if c { 1 } else { 2 } } else { 2 };\n";
    deep_else_defaults defaults
        "(else a (else a c))", "f(c) = a else (a else c);\n";
    deep_string_holes holes
        "(str (str 0))", "f(c) = \"${\"${0}\"}\";\n";
    deep_parameter_defaults lambda_defaults
        "(fn ((x = (fn ((x = 0)) x))) x)", "f(c) = (x = (x = 0) -> x) -> x;\n";
    deep_patterns patterns "(else e #a(#a(#a)) 0)", "f(c) = e else #a(#a(#a)) -> 0;\n";
    deep_field_patterns field_patterns
        "(else e #a(f: #a(f: #a)) 0)", "f(c) = e else #a(f: #a(f: #a)) -> 0;\n";
    deep_grouped_types grouped_types "(is x A)", "f(c) = x is A;\n";
    deep_function_types arrow_types
        "(is x (-> (A) (-> (A) B)))", "f(c) = x is (A -> A -> B);\n";
    deep_tuple_types tuple_types
        "(is x (tuple A (tuple A B)))", "f(c) = x is (A, (A, B));\n";
    deep_unions unions_in_groups
        "(is x (| A (| A B)))", "f(c) = x is A | (A | B);\n";
    a_long_difference differences
        "(is x (\\ (\\ A A) B))", "f(c) = x is A \\ A \\ B;\n";
    a_long_union long_union
        "(is x (| A A B))", "f(c) = x is A | A | B;\n";
}

/// A unit whose body is blocks of two statements nested `n` deep.
pub(super) fn nested_blocks(n: usize) -> String {
    format!("f(c) = {};\n", nest("{ y = ", "1", "; y }", n))
}

/// Blocks of two statements are written on lines of their own, each indented by its depth, so
/// the output itself has more than 2n² characters.
pub(super) fn writes_indented_lines(unit: &str, n: usize) {
    let out = format_source(unit.as_bytes()).unwrap();
    assert!(out.len() > 2 * n * n);
}

/// Their order is checked in `bench.rs`.
#[test]
fn deep_blocks_of_lines_are_written_each_on_its_own_line() {
    assert_eq!(
        format_source(nested_blocks(1).as_bytes()).unwrap(),
        "f(c) = {\n  y = 1;\n  y\n};\n"
    );
    for n in [2, 9, 40] {
        writes_indented_lines(&nested_blocks(n), n);
    }
}

/// A form of a later layer at the bottom of a deep nest is reported, with its own place.
#[test]
fn an_error_at_the_bottom_of_a_deep_nest_is_reported() {
    let text = nest("(", "x >< f unordered", ")", DEEP);
    let tokens = lex(&text).unwrap();
    let tree = parse(&text, &tokens, "Expr", TOP).unwrap();
    let e = build(&text, &tokens, &tree).unwrap_err();
    // The `unordered` starts 7 bytes after the `x`.
    assert_eq!(e.span.start, DEEP + 7);
    assert_eq!(
        e.message,
        zed_tests::not_yet!("the reduction order `unordered`")
    );
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
    let text = nest("\"${", "x >< f unordered", "}\"", DEEP);
    let tokens = lex(&text).unwrap();
    let tree = parse(&text, &tokens, "Expr", TOP).unwrap();
    let e = build(&text, &tokens, &tree).unwrap_err();
    assert_eq!(e.span.start, 3 * DEEP + 7);
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

/// No depth is too great: a nest of twenty thousand parentheses, a hundred times what the 2 MiB
/// stack held, is lexed, parsed, built, printed and dropped on the test thread's stack.
#[test]
fn twenty_thousand_parentheses() {
    let text = parens(20_000);
    let tokens = lex(&text).unwrap();
    let tree = parse(&text, &tokens, "Expr", TOP).unwrap();
    let e = build(&text, &tokens, &tree).unwrap();
    assert_eq!(e.to_string(), "1");
}
