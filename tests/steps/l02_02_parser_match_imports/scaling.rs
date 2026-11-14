//! The forms of this step at the rule of low complexity (DESIGN.md Part G): building,
//! formatting, refusing in name resolution and dropping a unit is linear in its size, for a
//! match of `n` arms, `n` imports, one import of `n` names, a pattern nested `n` deep and `n`
//! annotations. Each input is lexed and parsed before timing, so the work measured is this
//! step's, which the parser's own cost would otherwise hide. The benchmarks in `bench.rs` hold each
//! linear; here each is built, formatted and refused at small sizes.

use zedc::ast::unit;
use zedc::format::format;
use zedc::lex::{Token, lex};
use zedc::parse::{TOP, Tree, parse};
use zedc::resolve::resolve;

/// A unit's text, tokens and parse tree.
pub(super) struct Parsed {
    text: String,
    tokens: Vec<Token>,
    tree: Tree,
}

pub(super) fn parsed(text: String) -> Parsed {
    let tokens = lex(&text).unwrap();
    let tree = parse(&text, &tokens, "Unit", TOP).unwrap();
    Parsed { text, tokens, tree }
}

/// Builds, formats and resolves the unit `p`, and drops what it built. Resolution refuses
/// every form of this step; the refusals are part of the work.
pub(super) fn pass(p: &Parsed) {
    let stmts = unit(&p.text, &p.tokens, &p.tree).unwrap();
    std::hint::black_box(format(&p.text, &p.tokens, &stmts));
    assert!(resolve(&stmts).is_err());
}

/// `name(c) = match c { 0 -> "c0", k where k == 1 -> "c1", s is String -> …, … };`, `n` arms,
/// in turn a literal, a guard and a type pattern. At 1000 against 8000, a scan of the arms left
/// at each arm passed (20 times the work); at 4000 it fails (37 times).
pub(super) fn arms(n: usize) -> String {
    let arms: Vec<String> = (0..n)
        .map(|i| match i % 3 {
            0 => format!("{i} -> \"c{i}\""),
            1 => format!("k where k == {i} -> \"c{i}\""),
            _ => format!("s is String -> s ++ \"{i}\""),
        })
        .collect();
    format!("name(c) = match c {{ {} }};\n", arms.join(", "))
}

/// `n` imports in the three forms, every second one pinned.
pub(super) fn imports(n: usize) -> String {
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

/// `import lib.u.{a0, a1, …};`, one selective import of `n` names. At 1000 against 8000, a scan
/// of the names already seen in place of the duplicate check failed (58.4 times the work).
pub(super) fn one_import(n: usize) -> String {
    let names: Vec<String> = (0..n).map(|i| format!("a{i}")).collect();
    format!("import lib.u.{{{}}};\n", names.join(", "))
}

/// `f(t) = match t { #node(left: #node(left: … #leaf …, right: n is int), right: _) -> 0 };`,
/// a pattern nested `n` deep.
pub(super) fn deep(n: usize) -> String {
    format!(
        "f(t) = match t {{ {}#leaf{} -> 0 }};\n",
        "#node(left: ".repeat(n),
        ", right: n is int)".repeat(n)
    )
}

/// `n` functions, each with two annotations, one with arguments.
pub(super) fn annotated(n: usize) -> String {
    (0..n)
        .map(|i| format!("@cost(O(n * {i}), space: n) @memoized\nf{i}(n) = n + {i};\n"))
        .collect()
}

/// Every input of the benchmarks in `bench.rs` is built, formatted and refused in name
/// resolution at small sizes.
#[test]
fn each_form_is_built_formatted_and_refused_at_small_sizes() {
    for make in [arms, imports, one_import, deep, annotated] {
        for n in [1, 2, 9] {
            pass(&parsed(make(n)));
        }
    }
}
