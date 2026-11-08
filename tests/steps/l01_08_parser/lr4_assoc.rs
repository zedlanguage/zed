//! LR4, the associativity audit of sec:grammar (docs/grammar_assoc.md): each rule states its
//! associativity by left or right recursion, or by a repetition that its reader folds in the
//! direction the semantics needs. `a else b else c` and a chain of `&&`, `&& ?` and `&& !` joins
//! became left-recursive; every other rule kept its form.

use std::collections::HashMap;

use zed_tests::scaling::check;
use zed_tests::trees::sx;
use zedc::ast::build;
use zedc::format::format_source;
use zedc::lex::{Token, lex};
use zedc::parse::{TOP, parse};

/// The bracketing of `text` as `start`.
fn tree(text: &str, start: &str) -> String {
    let tokens = lex(text).unwrap();
    sx(text, &tokens, &parse(text, &tokens, start, TOP).unwrap())
}

/// The syntax tree of the expression `text`.
fn expr(text: &str) -> String {
    let tokens = lex(text).unwrap();
    let parsed = parse(text, &tokens, "Expr", TOP).unwrap();
    build(text, &tokens, &parsed).unwrap().to_string()
}

/// `f(c) = text;` as the formatter writes it.
fn written(text: &str) -> String {
    format_source(format!("f(c) = {text};\n").as_bytes()).unwrap()
}

/// One row of the audit table: the rule, where the text starts, the text and its bracketing.
const ROWS: &[(&str, &str, &str, &str)] = &[
    // Converted to left recursion.
    (
        "Expr12",
        "Expr",
        "a else b else c",
        "((a (else b)) (else c))",
    ),
    (
        "AndJoin",
        "Expr",
        "m into (a && !b && c -> v)",
        "(m (into ( (((a && ! b) && c) -> v) )))",
    ),
    // Left recursion already (LR2).
    ("Or", "Expr", "a || b || c", "((a || b) || c)"),
    ("And", "Expr", "a && b && c", "((a && b) && c)"),
    ("Additive", "Expr", "a - b + c", "((a - b) + c)"),
    ("Multiplicative", "Expr", "a / b * c", "((a / b) * c)"),
    (
        "Postfix",
        "Expr",
        "a.b(1)[0]",
        "(((a (. b)) (( 1 ))) ([ 0 ]))",
    ),
    ("Reduce", "Expr", "xs >< f >< g", "((xs (>< f)) (>< g))"),
    ("Path", "Item", "import a.b.c;", "(import ((a . b) . c) ;)"),
    (
        "KeyPath",
        "Expr",
        "s with { a.b = 1 }",
        "(s (with { (a . b = 1) }))",
    ),
    ("TypeOr", "Type", "A | B | C", "((A | B) | C)"),
    ("TypeAnd", "Type", "A & B & C", "((A & B) & C)"),
    ("TypeDiff", "Type", "int \\ 0 \\ 1", "((int \\ 0) \\ 1)"),
    (
        "TypePostfix",
        "Type",
        "int[0..<n][0..<m]",
        "((int ([ (0 ..< n) ])) ([ (0 ..< m) ]))",
    ),
    // Right recursion.
    ("Arrow", "Type", "A -> B -> C", "(A -> (B -> C))"),
    ("Prefix", "Expr", "- - x", "(- (- x))"),
    ("Power", "Expr", "2 ^ 3 ^ 2", "(2 ^ (3 ^ 2))"),
    ("TypeNot", "Type", "!!A", "(! (! A))"),
    ("Lambda", "Expr", "x -> y -> x + y", "(x -> (y -> (x + y)))"),
    (
        "If",
        "Expr",
        "if p { 1 } else if q { 2 } else { 3 }",
        "(if p ({ 1 }) else (if q ({ 2 }) else ({ 3 })))",
    ),
    // Conjunctions: every neighbor pair is compared.
    ("EqChain", "Expr", "a == b == c == d", "(a == b == c == d)"),
    ("AscChain", "Expr", "a < b <= c < d", "(a < b <= c < d)"),
    ("DescChain", "Expr", "a > b >= c", "(a > b >= c)"),
    // Lists.
    (
        "OutPattern",
        "Expr",
        "m into (a -> b -> c)",
        "(m (into ( (a -> b -> c) )))",
    ),
    (
        "InPattern",
        "Expr",
        "m as (a -> b -> c)",
        "(m (as ( (a -> b -> c) )))",
    ),
    (
        "JoinTerm ||",
        "Expr",
        "m into (a || b || c -> v)",
        "(m (into ( ((a || b || c) -> v) )))",
    ),
    (
        "Suffix* after with",
        "Expr",
        "p with { x = 1 }.norm.abs",
        "(p (with { (x = 1) } (. norm) (. abs)))",
    ),
    (
        "Update",
        "Expr",
        "s with { a.b.c = 1 }",
        "(s (with { (a . b . c = 1) }))",
    ),
    (
        "MoreGen",
        "Expr",
        "for x in xs, y in ys, z in zs { x }",
        "(for (x in xs) (, (y in ys)) (, (z in zs)) ({ x }))",
    ),
    (
        "TypeFacet",
        "Type",
        "T with f(1) with g(2)",
        "(T (with (f ( 1 ))) (with (g ( 2 ))))",
    ),
    (
        "GAlt",
        "Type",
        "String matching grammar { a | b | c }",
        "(String (matching (grammar { (a | b | c) })))",
    ),
    (
        "GSeq",
        "Type",
        "String matching grammar { a b c }",
        "(String (matching (grammar { (a b c) })))",
    ),
    (
        "IndexedDef",
        "Item",
        "f[i in D][j in E] = 0;",
        "(f [ (i in D) ] [ (j in E) ] = 0 ;)",
    ),
    (
        "KeyedPush",
        "Item",
        "f[a][b] <- 1;",
        "(f [ a ] [ b ] <- 1 ;)",
    ),
    (
        "Annotated",
        "Item",
        "@fused @memoized (a + b).map(f);",
        "(@fused @memoized ((((( (a + b) )) (. map)) (( f ))) ;))",
    ),
];

#[test]
fn every_rule_of_the_audit_nests_as_its_table_row_says() {
    let wrong: Vec<String> = ROWS
        .iter()
        .filter_map(|&(rule, start, text, want)| {
            let tokens = lex(text).unwrap();
            let got = match parse(text, &tokens, start, TOP) {
                Ok(t) => sx(text, &tokens, &t),
                Err(e) => format!("ERROR {e}"),
            };
            (got != want).then(|| format!("{rule} | {text}\n  got  {got}\n  want {want}"))
        })
        .collect();
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

#[test]
fn each_else_applies_to_the_expression_before_it() {
    assert_eq!(expr("a else b else c"), "(else (else a b) c)");
    assert_eq!(written("a else b else c"), "f(c) = a else b else c;\n");
}

#[test]
fn a_single_else_and_a_name_alone() {
    assert_eq!(expr("a else b"), "(else a b)");
    assert_eq!(expr("a"), "a");
}

#[test]
fn an_else_with_a_pattern_and_one_without_mix_from_the_left() {
    assert_eq!(
        tree("a else #x -> b else c", "Expr"),
        "((a (else #x -> b)) (else c))"
    );
    assert_eq!(expr("a else #x -> b else c"), "(else (else a #x b) c)");
}

#[test]
fn a_parenthesized_else_on_the_right_keeps_its_parentheses() {
    assert_eq!(expr("a else (b else c)"), "(else a (else b c))");
    assert_eq!(written("a else (b else c)"), "f(c) = a else (b else c);\n");
}

#[test]
fn a_chain_of_joins_of_mixed_kinds_joins_from_the_left() {
    assert_eq!(
        tree("m into (a && ?b && ?c -> v)", "Expr"),
        "(m (into ( (((a && ? b) && ? c) -> v) )))"
    );
    assert_eq!(
        tree("m into (a && !b && ?c && d -> v)", "Expr"),
        "(m (into ( ((((a && ! b) && ? c) && d) -> v) )))"
    );
}

#[test]
fn a_single_join_and_a_parenthesized_one_on_the_right() {
    assert_eq!(
        tree("m into (a && b -> v)", "Expr"),
        "(m (into ( ((a && b) -> v) )))"
    );
    assert_eq!(
        tree("m into (a && (b && !c) -> v)", "Expr"),
        "(m (into ( ((a && (( (b && ! c) ))) -> v) )))"
    );
}

/// `input(n)` at `n` and `8n`, lexed before the clock starts, then parsed as `start`.
fn scales(what: &str, start: &str, input: impl Fn(usize) -> String) {
    const N: usize = 2_000;
    let inputs: HashMap<usize, (String, Vec<Token>)> = [N, 8 * N]
        .into_iter()
        .map(|m| {
            let text = input(m);
            let tokens = lex(&text).unwrap();
            (m, (text, tokens))
        })
        .collect();
    check(what, N, |m| {
        let (text, tokens) = &inputs[&m];
        parse(text, tokens, start, TOP).unwrap();
    });
}

/// `n` copies of `part` between `before` and `after`, joined by `sep`.
fn chain(before: &str, part: &str, sep: &str, after: &str, n: usize) -> String {
    format!("{before}{}{after}", vec![part; n].join(sep))
}

macro_rules! scaling {
    ($($name:ident $start:literal $what:literal $input:expr;)*) => {
        $(
            #[test]
            fn $name() {
                scales($what, $start, $input);
            }
        )*
    };
}

scaling! {
    a_long_else_chain_is_linear "Expr" "an else chain of n tails" |n| chain("a", " else b", "", "", n);
    a_long_and_join_chain_is_linear "Expr" "a join of n keys" |n| chain("m into (", "a && !b", " && ", " -> v)", n);
    a_long_full_join_is_linear "Expr" "a full join of n keys" |n| chain("m into (", "a", " || ", " -> v)", n);
    a_long_equality_chain_is_linear "Expr" "an equality chain of n terms" |n| chain("", "a", " == ", "", n);
    a_long_ascending_chain_is_linear "Expr" "an ascending chain of n terms" |n| chain("", "a", " < ", "", n);
    a_long_out_pattern_is_linear "Expr" "an out pattern of n levels" |n| chain("m into (", "a", " -> ", ")", n);
    a_long_in_pattern_is_linear "Expr" "an in pattern of n levels" |n| chain("m as (", "a", " -> ", ")", n);
    a_long_sort_key_list_is_linear "Expr" "a level of n sort keys" |n| chain("m into (", "asc a", ", ", " -> v)", n);
    a_long_suffix_chain_after_with_is_linear "Expr" "n suffixes after with" |n| chain("p with { x = 1 }", ".a", "", "", n);
    a_long_update_path_is_linear "Expr" "an update path of n names" |n| chain("s with { ", "a", ".", " = 1 }", n);
    a_long_generator_list_is_linear "Expr" "n generators" |n| chain("for ", "x in xs", ", ", " { x }", n);
    a_long_facet_list_is_linear "Type" "n facets" |n| chain("T", " with f(1)", "", "", n);
    a_long_grammar_alternation_is_linear "Type" "a grammar of n alternatives" |n| chain("String matching grammar { ", "a", " | ", " }", n);
    a_long_grammar_sequence_is_linear "Type" "a grammar sequence of n items" |n| chain("String matching grammar { ", "a", " ", " }", n);
    a_long_indexed_definition_is_linear "Item" "a definition of n keys" |n| chain("f", "[i in D]", "", " = 0;", n);
    a_long_keyed_push_is_linear "Item" "a push of n keys" |n| chain("f", "[a]", "", " <- 1;", n);
    a_long_boundary_is_linear "Item" "a boundary of n items" |n| chain("x[t] = x[t - 1] with ", "x[0] = 0", ", ", ";", n);
    a_long_annotation_list_is_linear "Item" "n annotations" |n| chain("", "@fused", " ", " f(x) = x;", n);
}

/// The built tree of a long else chain, and its formatting, are linear too.
#[test]
fn a_long_else_chain_builds_and_formats_in_linear_time() {
    const N: usize = 2_000;
    let texts: HashMap<usize, String> = [N, 8 * N]
        .into_iter()
        .map(|m| (m, chain("a", " else b", "", "", m)))
        .collect();
    check("building an else chain of n tails", N, |m| {
        let text = &texts[&m];
        let tokens = lex(text).unwrap();
        let tree = parse(text, &tokens, "Expr", TOP).unwrap();
        build(text, &tokens, &tree).unwrap();
    });
    let units: HashMap<usize, String> = texts
        .iter()
        .map(|(&m, t)| (m, format!("f(c) = {t};\n")))
        .collect();
    check("formatting an else chain of n tails", N, |m| {
        format_source(units[&m].as_bytes()).unwrap();
    });
}

/// A hundred thousand else tails, and as many joins, on a thread of 8 MiB: the parser, the
/// builder, the formatter and the drop of the tree hold their work on the heap.
#[test]
fn a_hundred_thousand_else_tails_and_joins_on_an_8_mib_stack() {
    std::thread::Builder::new()
        .stack_size(8 << 20)
        .spawn(|| {
            const DEEP: usize = 100_000;
            let text = chain("a", " else b", "", "", DEEP);
            let tokens = lex(&text).unwrap();
            let tree = parse(&text, &tokens, "Expr", TOP).unwrap();
            let e = build(&text, &tokens, &tree).unwrap();
            assert!(e.to_string().starts_with(&"(else ".repeat(DEEP)));
            let unit = format!("f(c) = {text};\n");
            assert_eq!(format_source(unit.as_bytes()).unwrap(), unit);
            let joins = chain("m into (", "a && !b", " && ", " -> v)", DEEP);
            let tokens = lex(&joins).unwrap();
            parse(&joins, &tokens, "Expr", TOP).unwrap();
        })
        .unwrap()
        .join()
        .unwrap();
}
