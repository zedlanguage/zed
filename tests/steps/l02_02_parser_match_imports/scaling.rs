//! The forms of this step at the rule of low complexity (DESIGN.md Part G): building,
//! formatting, refusing in name resolution and dropping a unit is linear in its size, for a
//! match of `n` arms, `n` imports, one import of `n` names, a pattern nested `n` deep and `n`
//! annotations. Each input is lexed and parsed before timing, so the work measured is this
//! step's, which the parser's own cost would otherwise hide.

use std::collections::HashMap;

use zed_tests::scaling;
use zedc::ast::unit;
use zedc::format::format;
use zedc::lex::{Token, lex};
use zedc::parse::{TOP, Tree, parse};
use zedc::resolve::resolve;

/// A unit's text, tokens and parse tree.
struct Parsed {
    text: String,
    tokens: Vec<Token>,
    tree: Tree,
}

fn parsed(text: String) -> Parsed {
    let tokens = lex(&text).unwrap();
    let tree = parse(&text, &tokens, "Unit", TOP).unwrap();
    Parsed { text, tokens, tree }
}

/// Builds, formats and resolves the unit `p`, and drops what it built. Resolution refuses
/// every form of this step; the refusals are part of the work.
fn pass(p: &Parsed) {
    let stmts = unit(&p.text, &p.tokens, &p.tree).unwrap();
    std::hint::black_box(format(&p.text, &p.tokens, &stmts));
    assert!(resolve(&stmts).is_err());
}

/// Checks that `pass` over `make(n)` is linear in `n`, from `n` = `base`.
fn linear(what: &str, base: usize, make: impl Fn(usize) -> String) {
    let units: HashMap<usize, Parsed> = [base, 8 * base]
        .into_iter()
        .map(|n| (n, parsed(make(n))))
        .collect();
    scaling::check(what, base, |n| pass(&units[&n]));
}

/// `name(c) = match c { 0 -> "c0", k where k == 1 -> "c1", s is String -> …, … };`, `n` arms,
/// in turn a literal, a guard and a type pattern. At 1000 against 8000, a scan of the arms left
/// at each arm passed (20 times the work); at 4000 it fails (37 times).
fn arms(n: usize) -> String {
    let arms: Vec<String> = (0..n)
        .map(|i| match i % 3 {
            0 => format!("{i} -> \"c{i}\""),
            1 => format!("k where k == {i} -> \"c{i}\""),
            _ => format!("s is String -> s ++ \"{i}\""),
        })
        .collect();
    format!("name(c) = match c {{ {} }};\n", arms.join(", "))
}

#[test]
fn a_match_of_many_arms_scales() {
    linear("a match of n arms", 4000, arms);
}

/// `n` imports in the three forms, every second one pinned.
fn imports(n: usize) -> String {
    let pin = "@hash(\"0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef\")";
    (0..n)
        .map(|i| {
            let form = match i % 3 {
                0 => String::new(),
                1 => format!(" as m{i}"),
                _ => format!(".{{a{i}, b{i}}}"),
            };
            let pin = if i % 2 == 0 { pin } else { "" };
            format!("import lib.u{i}{form} {pin};\n")
        })
        .collect()
}

#[test]
fn many_imports_scale() {
    linear("n imports", 1000, imports);
}

/// `import lib.u.{a0, a1, …};`, one selective import of `n` names. At 1000 against 8000, a scan
/// of the names already seen in place of the duplicate check failed (58.4 times the work).
fn one_import(n: usize) -> String {
    let names: Vec<String> = (0..n).map(|i| format!("a{i}")).collect();
    format!("import lib.u.{{{}}};\n", names.join(", "))
}

#[test]
fn one_import_of_many_names_scales() {
    linear("one import of n names", 1000, one_import);
}

/// `f(t) = match t { #node(left: #node(left: … #leaf …, right: n is int), right: _) -> 0 };`,
/// a pattern nested `n` deep.
fn deep(n: usize) -> String {
    format!(
        "f(t) = match t {{ {}#leaf{} -> 0 }};\n",
        "#node(left: ".repeat(n),
        ", right: n is int)".repeat(n)
    )
}

#[test]
fn a_deep_pattern_scales() {
    linear("a match pattern nested n deep", 1000, deep);
}

/// `n` functions, each with two annotations, one with arguments.
fn annotated(n: usize) -> String {
    (0..n)
        .map(|i| format!("@cost(n * {i}, space: n) @memoized\nf{i}(n) = n + {i};\n"))
        .collect()
}

#[test]
fn many_annotations_scale() {
    linear("n annotated functions", 1000, annotated);
}
