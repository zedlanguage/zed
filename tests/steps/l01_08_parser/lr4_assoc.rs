//! LR4, the associativity audit of sec:grammar (docs/grammar_assoc.md): each rule states its
//! associativity by left or right recursion, or by a repetition that its reader folds in the
//! direction the semantics needs. `a else b else c` and a chain of `&&`, `&& ?` and `&& !` joins
//! became left-recursive; every other rule kept its form.

use zed_tests::trees::sx;
use zedc::ast::build;
use zedc::format::format_source;
use zedc::lex::lex;
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
    ("Power", "Expr", "2^3^2", "(2 ^ (3 ^ 2))"),
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

/// `n` copies of `part` between `before` and `after`, joined by `sep`.
fn chain(before: &str, part: &str, sep: &str, after: &str, n: usize) -> String {
    format!("{before}{}{after}", vec![part; n].join(sep))
}

/// A form of length `n` of one rule, parsed from `start`; `what` names it for its benchmark in
/// `bench/lr4_assoc.rs`.
pub(super) struct Long {
    pub(super) start: &'static str,
    pub(super) what: &'static str,
    pub(super) input: fn(usize) -> String,
}

macro_rules! long_forms {
    ($($name:ident $start:literal $what:literal $input:expr;)*) => {
        $(
            pub(super) const $name: Long = Long { start: $start, what: $what, input: $input };
        )*
        /// Every form of a rule written as a list or a left recursion.
        const LONG_FORMS: &[Long] = &[$($name),*];
    };
}

long_forms! {
    ELSE_CHAIN "Expr" "an else chain of n tails" |n| chain("a", " else b", "", "", n);
    AND_JOIN_CHAIN "Expr" "a join of n keys" |n| chain("m into (", "a && !b", " && ", " -> v)", n);
    FULL_JOIN "Expr" "a full join of n keys" |n| chain("m into (", "a", " || ", " -> v)", n);
    EQUALITY_CHAIN "Expr" "an equality chain of n terms" |n| chain("", "a", " == ", "", n);
    ASCENDING_CHAIN "Expr" "an ascending chain of n terms" |n| chain("", "a", " < ", "", n);
    OUT_PATTERN "Expr" "an out pattern of n levels" |n| chain("m into (", "a", " -> ", ")", n);
    IN_PATTERN "Expr" "an in pattern of n levels" |n| chain("m as (", "a", " -> ", ")", n);
    SORT_KEY_LIST "Expr" "a level of n sort keys" |n| chain("m into (", "asc a", ", ", " -> v)", n);
    SUFFIX_CHAIN_AFTER_WITH "Expr" "n suffixes after with" |n| chain("p with { x = 1 }", ".a", "", "", n);
    UPDATE_PATH "Expr" "an update path of n names" |n| chain("s with { ", "a", ".", " = 1 }", n);
    GENERATOR_LIST "Expr" "n generators" |n| chain("for ", "x in xs", ", ", " { x }", n);
    FACET_LIST "Type" "n facets" |n| chain("T", " with f(1)", "", "", n);
    GRAMMAR_ALTERNATION "Type" "a grammar of n alternatives" |n| chain("String matching grammar { ", "a", " | ", " }", n);
    GRAMMAR_SEQUENCE "Type" "a grammar sequence of n items" |n| chain("String matching grammar { ", "a", " ", " }", n);
    INDEXED_DEFINITION "Item" "a definition of n keys" |n| chain("f", "[i in D]", "", " = 0;", n);
    KEYED_PUSH "Item" "a push of n keys" |n| chain("f", "[a]", "", " <- 1;", n);
    BOUNDARY "Item" "a boundary of n items" |n| chain("x[t] = x[t - 1] with ", "x[0] = 0", ", ", ";", n);
    ANNOTATION_LIST "Item" "n annotations" |n| chain("", "@fused", " ", " f(x) = x;", n);
}

/// The long forms' benchmarks time their parse; here each parses at small lengths.
#[test]
fn each_long_form_parses_at_small_lengths() {
    for form in LONG_FORMS {
        for n in [1, 2, 9] {
            let text = (form.input)(n);
            let tokens = lex(&text).unwrap();
            if let Err(e) = parse(&text, &tokens, form.start, TOP) {
                panic!("{}, n = {n}: {e}", form.what);
            }
        }
    }
}

/// An else chain of `n` tails is built, and the formatter writes it back unchanged.
pub(super) fn builds_and_writes_back(text: &str) {
    let tokens = lex(text).unwrap();
    let tree = parse(text, &tokens, "Expr", TOP).unwrap();
    let e = build(text, &tokens, &tree).unwrap();
    assert!(e.to_string().starts_with("(else "));
    let unit = format!("f(c) = {text};\n");
    assert_eq!(format_source(unit.as_bytes()).unwrap(), unit);
}

#[test]
fn an_else_chain_is_built_and_written_back_at_small_lengths() {
    for n in [1, 2, 9] {
        builds_and_writes_back(&(ELSE_CHAIN.input)(n));
    }
}
