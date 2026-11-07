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

/// The files of the import cycles still open (item S.1f-rest), as `crate/path`. The tool reads
/// a call of a method written in another file than its type as an import (a Zed port makes that
/// `impl` block a unit of its own), and these files are in a cycle through such calls or through
/// paths: in zedc the `ast` builder split over five files, `check/mod.rs` and `check/walk.rs`
/// (one group of mutually recursive functions), `elab.rs` and `elab/walk.rs`, and
/// `store/presburger.rs` with `deep.rs` and `canon.rs`; in zed-kernel the type algebra in
/// `types`. The rest are in a cycle only through calls whose receiver the tool did not type,
/// each read as an import of every file with a method of that name. S.1f is done when this list
/// is empty and every crate passes the tool.
const KNOWN_CYCLES: &[&str] = &[
    "zed-kernel/num.rs",
    "zed-kernel/text.rs",
    "zed-kernel/types.rs",
    "zed-kernel/types/bdd.rs",
    "zed-kernel/types/bdd/list.rs",
    "zed-kernel/types/bes.rs",
    "zed-kernel/types/debug.rs",
    "zed-kernel/types/empty.rs",
    "zed-kernel/types/print.rs",
    "zed-kernel/types/rec.rs",
    "zed-kernel/types/rec/walk.rs",
    "zed-kernel/value.rs",
    "zedc/ast/body.rs",
    "zedc/ast/mod.rs",
    "zedc/ast/neglit.rs",
    "zedc/ast/stmts.rs",
    "zedc/ast/types.rs",
    "zedc/check/mod.rs",
    "zedc/check/ty.rs",
    "zedc/check/walk.rs",
    "zedc/check/widen.rs",
    "zedc/elab.rs",
    "zedc/elab/kernel_type.rs",
    "zedc/elab/tables.rs",
    "zedc/elab/walk.rs",
    "zedc/parse/engine.rs",
    "zedc/parse/mod.rs",
    "zedc/resolve.rs",
    "zedc/stage.rs",
    "zedc/store/int.rs",
    "zedc/store/interval.rs",
    "zedc/store/landmarks.rs",
    "zedc/store/lattice.rs",
    "zedc/store/linear.rs",
    "zedc/store/live3.rs",
    "zedc/store/negsssp.rs",
    "zedc/store/presburger.rs",
    "zedc/store/presburger/deep.rs",
    "zedc/store/presburger/deep/canon.rs",
    "zedc/store/presburger/formula.rs",
    "zedc/store/revision.rs",
    "zedc/store/twovar.rs",
    "zedc/store/utvpi.rs",
    "zedc/work.rs",
];

#[test]
fn no_crate_has_an_import_cycle_but_the_known_ones() {
    let root = zed_tools::impl_root();
    let mut crates: Vec<String> = std::fs::read_dir(format!("{root}/crates"))
        .expect("the crates directory")
        .map(|e| {
            e.expect("a crate")
                .file_name()
                .into_string()
                .expect("a UTF-8 name")
        })
        .filter(|c| std::path::Path::new(&format!("{root}/crates/{c}/src")).is_dir())
        .collect();
    crates.sort();
    assert!(crates.len() >= 5, "{crates:?}");
    let mut new = Vec::new();
    for c in &crates {
        let dir = format!("{root}/crates/{c}/src");
        let files = imports::read_sources(&dir).expect("the crate's sources");
        let g = Graph::of(&files).expect("the crate's graph");
        assert_eq!(g.undeclared, 0, "{c}: {:?}", g.files);
        for component in g.cycles() {
            for f in component {
                let at = format!("{c}/{}", g.files[f]);
                if !KNOWN_CYCLES.contains(&at.as_str()) {
                    new.push(at);
                }
            }
        }
    }
    assert!(
        new.is_empty(),
        "files in an import cycle not known to be: {new:?}"
    );
    // The graph is the compiler's, not an empty one: every file is reached, with its imports.
    let dir = format!("{root}/crates/zedc/src");
    let files = imports::read_sources(&dir).expect("the compiler's sources");
    let g = Graph::of(&files).expect("the compiler's graph");
    assert!(g.files.len() > 60, "{} files", g.files.len());
    assert!(
        edges(&g).len() > g.files.len(),
        "{} imports",
        edges(&g).len()
    );
    // A crate with no open cycle passes the tool itself.
    let dir = format!("{root}/crates/zed-native/src");
    let (outcome, out) = tool(imports::run, &[&dir]);
    assert_eq!(outcome, Ok(true), "{out}");
    assert!(out.ends_with("no import cycle\n"), "{out}");
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

#[test]
fn a_call_of_a_method_written_apart_imports_its_file() {
    // `Builder` is defined in `build.rs` and has a method in `more.rs`: a Zed port makes that
    // block a unit of its own, so the caller of `b.more()` imports `more.rs`, and `more.rs`
    // calling back into `build.rs` closes a cycle. A method written with its type draws no
    // edge of its own.
    let files = |more: &str| {
        graph(&[
            ("lib.rs", "mod build;\nmod more;\n"),
            (
                "build.rs",
                "pub struct Builder;\nimpl Builder {\n    pub fn own(&self) {}\n}\n\
                 pub fn run(b: &Builder) { b.own(); b.more(); }\n",
            ),
            ("more.rs", more),
        ])
    };
    let g = files("use crate::build::Builder;\nimpl Builder {\n    pub fn more(&self) {}\n}\n");
    assert_eq!(edges(&g), ["build.rs -> more.rs", "more.rs -> build.rs"]);
    assert_eq!(cycles(&g), [["build.rs", "more.rs"]]);
    assert_eq!(g.unknown_calls, 0);
}

#[test]
fn the_receiver_is_typed_through_patterns_closures_and_wrappers() {
    // Each call's receiver is typed, so only `A::m` (in `am.rs`) is drawn, never `B::m` (in
    // `bm.rs`), and no call falls back to every file with an `m`.
    let user = "use std::collections::HashMap;\nuse crate::t::{A, B};\n\
        pub struct Holder { pub a: Option<Box<A>>, pub b: B }\n\
        pub fn f(h: &Holder, map: &HashMap<u32, Vec<A>>, xs: &[(u32, A)]) {\n\
        \x20   if let Some(a) = &h.a { a.m(); }\n\
        \x20   for (_, v) in map.iter() { for a in v { a.m(); } }\n\
        \x20   xs.iter().for_each(|(_, a)| a.m());\n\
        \x20   for (i, (_, a)) in xs.iter().enumerate() { let _ = i; a.m(); }\n\
        \x20   match map.get(&0) { Some(v) => v[0].m(), None => {} }\n\
        \x20   let (_, a) = &xs[0];\n\x20   a.m();\n\
        }\n";
    let g = graph(&[
        ("lib.rs", "mod t;\nmod am;\nmod bm;\nmod user;\n"),
        ("t.rs", "pub struct A;\npub struct B;\n"),
        (
            "am.rs",
            "use crate::t::A;\nimpl A {\n    pub fn m(&self) {}\n}\n",
        ),
        (
            "bm.rs",
            "use crate::t::B;\nimpl B {\n    pub fn m(&self) {}\n}\n",
        ),
        ("user.rs", user),
    ]);
    assert_eq!(
        edges(&g),
        [
            "am.rs -> t.rs",
            "bm.rs -> t.rs",
            "user.rs -> t.rs",
            "user.rs -> am.rs"
        ]
    );
    assert_eq!(g.unknown_calls, 0);
}

#[test]
fn an_untyped_receiver_imports_every_file_it_may_call() {
    // `y` is the value of another crate's function, whose type the tool does not know: the
    // call imports every file with a method `m` written apart from its type that `user.rs` may
    // call. The private one in `hidden.rs` is out of its reach, and the associated function
    // `C::m` is called by path, never as `y.m()`. On `x`, of a type parameter's type, only the
    // methods of its bounds' traits can be called, so `x.m()` imports nothing.
    let g = graph(&[
        (
            "lib.rs",
            "mod t;\nmod am;\nmod bm;\nmod hidden;\nmod cm;\nmod user;\n",
        ),
        (
            "t.rs",
            "pub struct A;\npub struct B;\npub struct C;\npub struct D;\n",
        ),
        (
            "am.rs",
            "use crate::t::A;\nimpl A {\n    pub fn m(&self) {}\n}\n",
        ),
        (
            "bm.rs",
            "use crate::t::B;\nimpl B {\n    pub fn m(&mut self) {}\n}\n",
        ),
        (
            "hidden.rs",
            "use crate::t::D;\nimpl D {\n    fn m(&self) {}\n}\n",
        ),
        (
            "cm.rs",
            "use crate::t::C;\nimpl C {\n    pub fn m() {}\n}\n",
        ),
        (
            "user.rs",
            "pub fn f<T>(x: T) { x.m(); }\npub fn g() { let y = other::make(); y.m(); }\n",
        ),
    ]);
    let from_user: Vec<String> = edges(&g)
        .into_iter()
        .filter(|e| e.starts_with("user.rs"))
        .collect();
    assert_eq!(from_user, ["user.rs -> am.rs", "user.rs -> bm.rs"]);
    assert_eq!(g.unknown_calls, 1);
    // Called by its path, the associated function draws its own file.
    let by_path = graph(&[
        ("lib.rs", "mod t;\nmod cm;\nmod user;\n"),
        ("t.rs", "pub struct C;\n"),
        (
            "cm.rs",
            "use crate::t::C;\nimpl C {\n    pub fn m() {}\n}\n",
        ),
        ("user.rs", "use crate::t::C;\npub fn f() { C::m(); }\n"),
    ]);
    assert_eq!(
        edges(&by_path),
        ["cm.rs -> t.rs", "user.rs -> t.rs", "user.rs -> cm.rs"]
    );
}

/// A crate of `n` types `T0` to `T{n-1}`, each in a file `t{i}.rs` with its one method `go`
/// written apart in `m{i}.rs`, which calls `go` on a `T{i+1}`, the last on a `T0`: the `m`
/// files are one cycle of `n` files, through calls alone.
fn method_ring(n: usize) -> Vec<(String, String)> {
    let mut files = Vec::new();
    for i in 0..n {
        let next = (i + 1) % n;
        files.push((format!("t{i}.rs"), format!("pub struct T{i};\n")));
        let text = format!(
            "use crate::t{i}::T{i};\nuse crate::t{next}::T{next};\n\nimpl T{i} {{\n    \
             pub fn go(&self, x: &T{next}) {{\n        let y: Option<&T{next}> = Some(x);\n        \
             if let Some(z) = y {{\n            z.go(&crate::t0::T0);\n        }}\n    }}\n}}\n"
        );
        files.push((format!("m{i}.rs"), text));
    }
    let lib: String = (0..n).map(|i| format!("mod t{i};\nmod m{i};\n")).collect();
    files.push(("lib.rs".to_string(), lib));
    files.sort();
    files
}

#[test]
fn typing_the_calls_scales_with_the_number_of_files() {
    // Every type has a method of the same name, so a call whose receiver went untyped would
    // import all n files with it, n^2 imports in all; typed, each call is one hash lookup.
    let n = 200;
    let inputs = [method_ring(n), method_ring(8 * n)];
    check("imports, by methods written apart in one cycle", n, |m| {
        let files = inputs
            .iter()
            .find(|f| f.len() == 2 * m + 1)
            .expect("a size that was built");
        let g = Graph::of(files).expect("the ring's graph");
        assert_eq!(g.unknown_calls, 0);
        let found = g.cycles();
        assert_eq!(found.len(), 1);
        assert_eq!(found[0].len(), m);
    });
}
