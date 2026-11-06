//! Step S.1f: the Rust-hosted compiler's file import graph is acyclic, since Zed forbids a cycle
//! between files (sec:units), and the checked-in tool `imports` builds the graph and names every
//! cycle (`zed_tools::imports`).

use zed_tests::scaling::check;
use zed_tools::imports::{self, Graph};

use zed_tests::step_helpers::m0_03_grammar_tools::{Dir, tool};

/// The graph of `files`, each a path and its text.
fn graph(files: &[(&str, &str)]) -> Graph {
    let files: Vec<(String, String)> = files
        .iter()
        .map(|&(p, t)| (p.to_string(), t.to_string()))
        .collect();
    Graph::of(&files).expect("a crate whose `mod` declarations name files")
}

/// The imports of `g`, each as `from -> to`, in order.
fn edges(g: &Graph) -> Vec<String> {
    let mut all = Vec::new();
    for (f, list) in g.imports.iter().enumerate() {
        for (t, _) in list {
            all.push(format!("{} -> {}", g.files[f], g.files[*t]));
        }
    }
    all
}

/// The cycles of `g`, each as its files.
fn cycles(g: &Graph) -> Vec<Vec<&str>> {
    g.cycles()
        .iter()
        .map(|c| c.iter().map(|&f| g.files[f].as_str()).collect())
        .collect()
}

#[test]
fn the_compiler_has_no_import_cycle() {
    let dir = format!("{}/crates/zedc/src", zed_tools::impl_root());
    let (outcome, out) = tool(imports::run, &[&dir]);
    assert_eq!(outcome, Ok(true), "{out}");
    assert!(out.ends_with("no import cycle\n"), "{out}");
    // The graph is the compiler's, not an empty one: every file is reached, with its imports.
    let files = imports::read_sources(&dir).expect("the compiler's sources");
    let g = Graph::of(&files).expect("the compiler's graph");
    assert_eq!(g.undeclared, 0, "{:?}", g.files);
    assert!(g.files.len() > 60, "{} files", g.files.len());
    assert!(
        edges(&g).len() > g.files.len(),
        "{} imports",
        edges(&g).len()
    );
}

#[test]
fn a_cycle_makes_the_tool_fail_and_is_named() {
    let dir = Dir::new("s1f_cycle");
    dir.write(
        "lib.rs",
        "pub mod parse;\npub mod check;\npub mod print;\npub mod span;\n",
    );
    dir.write("span.rs", "pub struct Span(pub usize);\n");
    dir.write(
        "parse.rs",
        "use crate::span::Span;\n\npub fn parse(s: &str) -> crate::check::Checked {\n    \
         crate::check::check(Span(s.len()))\n}\n",
    );
    dir.write(
        "check.rs",
        "pub struct Checked;\n\npub fn check(_: crate::span::Span) -> Checked {\n    \
         super::print::show(\"x\");\n    Checked\n}\n",
    );
    dir.write(
        "print.rs",
        "use crate::parse;\n\npub fn show(s: &str) {\n    let _ = parse::parse(s);\n}\n",
    );
    let (outcome, out) = tool(imports::run, &[&dir.root()]);
    // `main_of` exits with 1 on `Ok(false)`.
    assert_eq!(outcome, Ok(false), "{out}");
    let expected = format!(
        "{}: 5 files, 5 imports between files\n\
         cycle 1 of 1: 3 files: check.rs, parse.rs, print.rs\n  \
         a shortest cycle through check.rs:\n    \
         check.rs:4 super::print::show -> print.rs\n    \
         print.rs:4 parse::parse -> parse.rs\n    \
         parse.rs:3 crate::check::Checked -> check.rs\n  \
         every import within it:\n    \
         check.rs:4 super::print::show -> print.rs\n    \
         parse.rs:3 crate::check::Checked -> check.rs\n    \
         print.rs:4 parse::parse -> parse.rs\n",
        dir.root()
    );
    assert_eq!(out, expected);
}

#[test]
fn a_parent_and_its_child_form_a_cycle() {
    // A `mod` declaration is no import, but the parent naming the child's item and the child
    // naming the parent's are.
    let g = graph(&[
        ("lib.rs", "mod lex;\n"),
        (
            "lex/mod.rs",
            "mod number;\npub struct Span;\nfn f() { number::number(); }\n",
        ),
        (
            "lex/number.rs",
            "use super::Span;\npub fn number() -> Option<Span> { None }\n",
        ),
    ]);
    assert_eq!(cycles(&g), [["lex/mod.rs", "lex/number.rs"]]);
    let no_child_use = graph(&[
        ("lib.rs", "mod lex;\n"),
        ("lex/mod.rs", "mod number;\npub struct Span;\n"),
        ("lex/number.rs", "use super::Span;\n"),
    ]);
    assert_eq!(edges(&no_child_use), ["lex/number.rs -> lex/mod.rs"]);
    assert!(cycles(&no_child_use).is_empty());
}

#[test]
fn a_re_export_leads_to_the_defining_file() {
    // `ast/mod.rs` re-exports `Expr` from `ast/expr.rs`; a user of `crate::ast::Expr` imports
    // `ast/expr.rs`, and the re-export is the parent's import of its child.
    let g = graph(&[
        ("lib.rs", "pub mod ast;\npub mod check;\n"),
        (
            "ast/mod.rs",
            "mod expr;\npub use expr::{Expr, Kind as ExprKind};\n",
        ),
        ("ast/expr.rs", "pub struct Expr;\npub enum Kind { A }\n"),
        (
            "check.rs",
            "use crate::ast::{self, Expr};\nfn f(_: Expr) -> ast::ExprKind { ast::ExprKind::A }\n",
        ),
    ]);
    assert_eq!(
        edges(&g),
        ["ast/mod.rs -> ast/expr.rs", "check.rs -> ast/expr.rs"]
    );
}

#[test]
fn text_that_is_not_code_names_nothing() {
    // Paths in comments, strings, raw strings and characters, a lifetime named like a keyword,
    // and a module named but never used are no imports.
    let g = graph(&[
        ("lib.rs", "mod a;\nmod b;\n"),
        ("a.rs", "pub struct A;\npub fn f<'a>(_: &'a str) {}\n"),
        (
            "b.rs",
            "use crate::a;\n// crate::a::A\n/* crate::a::A /* nested */ crate::a::f */\n\
             const S: &str = \"crate::a::A\";\nconst R: &str = r#\"crate::a::A\"#;\n\
             const C: char = '\"';\nfn g<'static_like>() {}\n",
        ),
    ]);
    assert!(edges(&g).is_empty(), "{:?}", edges(&g));
}

#[test]
fn a_test_module_names_its_own_file() {
    // `use super::*;` in an inline module names the file it is written in, which is no import;
    // a glob of another module is an import of that module's file.
    let g = graph(&[
        ("lib.rs", "mod a;\nmod b;\n"),
        (
            "a.rs",
            "pub fn f() {}\n#[cfg(test)]\nmod tests {\n    use super::*;\n}\n",
        ),
        ("b.rs", "use crate::a::*;\nfn g() { f() }\n"),
    ]);
    assert_eq!(edges(&g), ["b.rs -> a.rs"]);
}

#[test]
fn an_undeclared_file_is_left_out() {
    let g = graph(&[
        ("lib.rs", "mod a;\n"),
        ("a.rs", ""),
        ("old.rs", "use crate::a::X;\n"),
    ]);
    assert_eq!(g.files, ["lib.rs", "a.rs"]);
    assert_eq!(g.undeclared, 1);
}

#[test]
fn a_module_a_path_attribute_places_is_not_read() {
    // `zed-kernel` reads the shared scaling test from `tests/src` this way: the file is outside
    // the crate, so a path through the module leads outside the graph, not to the declaring file.
    let g = graph(&[
        (
            "lib.rs",
            "pub mod a;\n#[cfg(test)]\n#[path = \"../../tests/src/scaling.rs\"]\nmod scaling;\n",
        ),
        (
            "a.rs",
            "use crate::scaling::check;\nfn f() { check(); crate::scaling::order(); }\n",
        ),
    ]);
    assert_eq!(g.placed, ["lib.rs:4"]);
    assert!(edges(&g).is_empty(), "{:?}", edges(&g));
}

#[test]
fn a_missing_module_file_is_an_error() {
    let files = vec![("lib.rs".to_string(), "mod gone;\n".to_string())];
    assert_eq!(
        Graph::of(&files).map(|g| g.files),
        Err("lib.rs:1: `mod gone;` names no file".to_string())
    );
}

/// A crate of `n` files, `m0` to `m{n-1}`, each naming the next, the last naming the first, so
/// the whole is one cycle of `n` files whose shortest cycle has them all.
fn ring(n: usize) -> Vec<(String, String)> {
    let mut files: Vec<(String, String)> = (0..n)
        .map(|i| {
            let next = (i + 1) % n;
            let text = format!(
                "use crate::m{next}::T{next};\n\npub struct T{i};\n\npub fn f{i}(_: T{next}) -> \
                 crate::m{next}::T{next} {{\n    crate::m{next}::T{next}\n}}\n"
            );
            (format!("m{i}.rs"), text)
        })
        .collect();
    let lib: String = (0..n).map(|i| format!("pub mod m{i};\n")).collect();
    files.push(("lib.rs".to_string(), lib));
    files.sort();
    files
}

#[test]
fn the_tool_scales_with_the_number_of_files() {
    // Inputs are built before timing. The ring is one long component, so Tarjan's explicit
    // stack is as deep as the crate is large, and the report names all n files twice.
    let n = 400;
    let inputs = [ring(n), ring(8 * n)];
    check("imports, by files in one cycle", n, |m| {
        let files = inputs
            .iter()
            .find(|f| f.len() == m + 1)
            .expect("a size that was built");
        let g = Graph::of(files).expect("the ring's graph");
        let found = g.cycles();
        assert_eq!(found.len(), 1);
        assert_eq!(g.shortest_cycle(&found[0]).len(), m);
    });
}
