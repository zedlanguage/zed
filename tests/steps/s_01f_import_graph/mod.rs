//! Step S.1f: the Rust-hosted compiler's file import graph is acyclic, since Zed forbids a cycle
//! between files (sec:units), and the checked-in tool `imports` builds the graph and names every
//! cycle (`zed_tools::imports`).

use std::collections::HashSet;

use zed_tests::scaling::{check, check_order};
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
/// paths. The compiler (zedc and the crates zedc-* it is split into) has none since
/// CYCLE-zedc-moves, and zed-kernel none since CYCLE-kernel-moves (ZED_PORT_GAPS.md gap 10), so
/// the list is empty: S.1f is done once every crate passes the tool.
const KNOWN_CYCLES: &[&str] = &[];

/// Appends the files of `g`'s import cycles to `found`, each as `crate/path` with `c` the crate.
fn files_in_cycles(c: &str, g: &Graph, found: &mut Vec<String>) {
    for component in g.cycles() {
        for f in component {
            found.push(format!("{c}/{}", g.files[f]));
        }
    }
}

/// The files of `found` that `known` does not list, and the entries of `known` that name no
/// file of `found`, each in the order given. An entry of the second kind is stale: its cycle
/// was broken, or its file moved or deleted, and the list would otherwise keep it forever. Each
/// file and entry is one hash lookup.
fn against_known<'k>(known: &[&'k str], found: &[String]) -> (Vec<String>, Vec<&'k str>) {
    let listed: HashSet<&str> = known.iter().copied().collect();
    let cyclic: HashSet<&str> = found.iter().map(String::as_str).collect();
    let new = found
        .iter()
        .filter(|f| !listed.contains(f.as_str()))
        .cloned()
        .collect();
    let stale = known
        .iter()
        .copied()
        .filter(|k| !cyclic.contains(k))
        .collect();
    (new, stale)
}

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
    let mut found = Vec::new();
    for c in &crates {
        let dir = format!("{root}/crates/{c}/src");
        let files = imports::read_sources(&dir).expect("the crate's sources");
        let g = Graph::of(&files).expect("the crate's graph");
        assert_eq!(g.undeclared, 0, "{c}: {:?}", g.files);
        files_in_cycles(c, &g, &mut found);
    }
    let (new, stale) = against_known(KNOWN_CYCLES, &found);
    assert!(
        new.is_empty(),
        "files in an import cycle not known to be: {new:?}"
    );
    assert!(
        stale.is_empty(),
        "KNOWN_CYCLES lists files in no import cycle; remove them: {stale:?}"
    );
    // The graphs are the compiler's, not empty ones: every file is reached, with its imports.
    // The compiler is the crate `zedc` and the crates `zedc-*` it is split into, and none of
    // them has a cycle (CYCLE-zedc-moves).
    let (mut file_count, mut import_count) = (0, 0);
    for dir in zed_tools::compiler_dirs(&root).expect("the compiler's crates") {
        let sources = imports::read_sources(&dir).expect("the compiler's sources");
        let g = Graph::of(&sources).expect("the compiler's graph");
        assert!(g.cycles().is_empty(), "{dir}: {:?}", cycles(&g));
        file_count += g.files.len();
        import_count += edges(&g).len();
    }
    assert!(file_count > 60, "{file_count} files");
    assert!(import_count > file_count, "{import_count} imports");
    // A crate with no open cycle passes the tool itself.
    for name in ["zed-native", "zed-kernel"] {
        let dir = format!("{root}/crates/{name}/src");
        let (outcome, out) = tool(imports::run, &[&dir]);
        assert_eq!(outcome, Ok(true), "{out}");
        assert!(out.ends_with("no import cycle\n"), "{out}");
    }
}

#[test]
fn a_listed_file_outside_every_cycle_is_reported() {
    // `build.rs` and `more.rs` call each other; `lib.rs` is in no cycle. A list written when
    // `lib.rs` was in the cycle, and naming a crate since renamed, has two stale entries, and
    // `more.rs`, which it leaves out, is new.
    let g = graph(&[
        ("lib.rs", "mod build;\nmod more;\n"),
        (
            "build.rs",
            "pub struct Builder;\npub fn run(b: &Builder) { b.more(); }\n",
        ),
        (
            "more.rs",
            "use crate::build::Builder;\nimpl Builder {\n    pub fn more(&self) { crate::build::run(self); }\n}\n",
        ),
    ]);
    let mut found = Vec::new();
    files_in_cycles("tool", &g, &mut found);
    assert_eq!(found, ["tool/build.rs", "tool/more.rs"]);
    let known = ["tool/lib.rs", "tool/build.rs", "old-tool/build.rs"];
    let (new, stale) = against_known(&known, &found);
    assert_eq!(new, ["tool/more.rs"]);
    assert_eq!(stale, ["tool/lib.rs", "old-tool/build.rs"]);
    // The exact list passes both ways; an empty list with no cycle passes too.
    let exact = ["tool/more.rs", "tool/build.rs"];
    assert_eq!(against_known(&exact, &found), (vec![], vec![]));
    assert_eq!(against_known(&[], &[]), (vec![], vec![]));
    // Every entry is stale once the cycle is broken.
    assert_eq!(against_known(&exact, &[]), (vec![], exact.to_vec()));
}

#[test]
fn comparing_with_the_known_list_scales_with_its_length() {
    // Inputs are built before timing: n files in cycles and a list of n entries, half of them
    // the files, half stale, so both directions are searched in full.
    let n = 20_000;
    let sizes = [n, 8 * n];
    let inputs: Vec<(Vec<String>, Vec<String>)> = sizes
        .iter()
        .map(|&m| {
            let found = (0..m).map(|i| format!("c/f{i}.rs")).collect();
            let known = (0..m)
                .map(|i| format!("c/f{}.rs", if i % 2 == 0 { i } else { m + i }))
                .collect();
            (found, known)
        })
        .collect();
    let lists: Vec<Vec<&str>> = inputs
        .iter()
        .map(|(_, k)| k.iter().map(String::as_str).collect())
        .collect();
    check("against_known, by files and entries", n, |m| {
        let at = sizes
            .iter()
            .position(|&s| s == m)
            .expect("a size that was built");
        let (new, stale) = against_known(&lists[at], &inputs[at].0);
        assert_eq!((new.len(), stale.len()), (m / 2, m / 2));
    });
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
fn an_untyped_receiver_imports_the_files_it_may_call_through_its_type_file() {
    // `y` is the value of another crate's function, whose type the tool does not know. `user.rs`
    // imports `t.rs`, where `A` to `D` are defined, so the call imports every file with a method
    // `m` of one of them, written apart, that `user.rs` may call. The private one in `hidden.rs`
    // is out of its reach, and the associated function `C::m` is called by path, never as
    // `y.m()`. On `x`, of a type parameter's type, only the methods of its bounds' traits can be
    // called, so `x.m()` imports nothing.
    let crate_with = |user: &str| {
        graph(&[
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
            ("user.rs", user),
        ])
    };
    let from_user = |g: &Graph| -> Vec<String> {
        edges(g)
            .into_iter()
            .filter(|e| e.starts_with("user.rs"))
            .collect()
    };
    let calls = "pub fn f<T>(x: T) { x.m(); }\npub fn g() { let y = other::make(); y.m(); }\n";
    let g = crate_with(&format!("pub fn h(_: &crate::t::A) {{}}\n{calls}"));
    assert_eq!(
        from_user(&g),
        ["user.rs -> t.rs", "user.rs -> am.rs", "user.rs -> bm.rs"]
    );
    assert_eq!(g.unknown_calls, 1);
    // Without the import of `t.rs` the name `m` alone imports nothing: `y` is no value of a
    // type of `t.rs` that `user.rs` could name.
    let g = crate_with(calls);
    assert!(from_user(&g).is_empty(), "{:?}", from_user(&g));
    assert_eq!(g.unknown_calls, 0);
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

#[test]
fn an_untyped_receiver_imports_only_through_its_type_file() {
    // A real cycle through an untyped call is still found: `user.rs` names `S`, of `t.rs`, and
    // calls `go` on a value the tool does not type; `go` is written in `sm.rs`, which calls back
    // into `user.rs`.
    let g = graph(&[
        ("lib.rs", "mod t;\nmod sm;\nmod user;\n"),
        ("t.rs", "pub struct S;\n"),
        (
            "sm.rs",
            "use crate::t::S;\nimpl S {\n    pub fn go(&self) { crate::user::back(); }\n}\n",
        ),
        (
            "user.rs",
            "use crate::t::S;\npub fn back() {}\n\
             pub fn f(_: &S) { let (s, _) = (other::make(), 0); s.go(); }\n",
        ),
    ]);
    assert_eq!(
        edges(&g),
        [
            "sm.rs -> t.rs",
            "sm.rs -> user.rs",
            "user.rs -> t.rs",
            "user.rs -> sm.rs"
        ]
    );
    assert_eq!(cycles(&g), [["sm.rs", "user.rs"]]);
    assert_eq!(g.unknown_calls, 1);
    // The false cycle of zed-kernel's `types/bucket.rs`: `stack` is a `Vec`, from a tuple `let`
    // the tool does not type, in a file that imports nothing of `t.rs`. `Bucket::is_empty`,
    // written in `empty.rs`, which calls into `scan.rs`, shares only its name, so `scan.rs`
    // does not import `empty.rs` and there is no cycle.
    let crate_with = |scan: &str| {
        graph(&[
            ("lib.rs", "mod t;\nmod empty;\nmod scan;\n"),
            ("t.rs", "pub struct Bucket;\n"),
            (
                "empty.rs",
                "use crate::t::Bucket;\nimpl Bucket {\n    \
                 pub fn is_empty(&self) -> bool { crate::scan::count() == 0 }\n}\n",
            ),
            ("scan.rs", scan),
        ])
    };
    let untyped = "pub fn count() -> usize {\n    let (mut stack, at) = (Vec::new(), 0);\n    \
                   stack.push(at);\n    if stack.is_empty() { 0 } else { 1 }\n}\n";
    let g = crate_with(untyped);
    assert_eq!(edges(&g), ["empty.rs -> t.rs", "empty.rs -> scan.rs"]);
    assert!(cycles(&g).is_empty(), "{:?}", cycles(&g));
    assert_eq!(g.unknown_calls, 0);
    // Typed as a `Bucket`, the same call imports `empty.rs`, and the cycle is real.
    let typed = "use crate::t::Bucket;\npub fn count() -> usize { 0 }\n\
                 pub fn f(b: &Bucket) -> bool { b.is_empty() }\n";
    let g = crate_with(typed);
    assert_eq!(cycles(&g), [["empty.rs", "scan.rs"]]);
    // Given up (the tradeoff of `untyped_imports`): the type's own file calling the method on
    // an untyped receiver imports nothing, since a file never imports itself, though here the
    // receiver might be a `Bucket`.
    let own = graph(&[
        ("lib.rs", "mod t;\nmod empty;\n"),
        (
            "t.rs",
            "pub struct Bucket;\npub fn f() -> bool { let (b, _) = (other::make(), 0); \
             b.is_empty() }\n",
        ),
        (
            "empty.rs",
            "use crate::t::Bucket;\nimpl Bucket {\n    \
             pub fn is_empty(&self) -> bool { crate::t::f() }\n}\n",
        ),
    ]);
    assert_eq!(edges(&own), ["empty.rs -> t.rs"]);
    assert_eq!(own.unknown_calls, 0);
}

#[test]
fn a_word_after_a_range_starts_a_chain() {
    // The false cycle of zed-kernel's `text/names.rs` (IMPORT-cycle-kernel-text): `ids` is a
    // slice parameter, and `..ids.len()` calls the slice's `len`, never `A::len`, written apart
    // in `am.rs`, though `user.rs` imports `t.rs`. Nor is `..count()` a method call.
    let crate_with = |body: &str| {
        graph(&[
            ("lib.rs", "mod t;\nmod am;\nmod user;\n"),
            ("t.rs", "pub struct A;\n"),
            (
                "am.rs",
                "use crate::t::A;\nimpl A {\n    pub fn len(&self) -> usize { 0 }\n    \
                 pub fn count(&self) -> usize { 0 }\n}\n",
            ),
            (
                "user.rs",
                &format!(
                    "use crate::t::A;\npub fn count() -> usize {{ 1 }}\n\
                     pub fn f(_: &A, ids: &[u64]) -> usize {{\n    {body}\n}}\n"
                ),
            ),
        ])
    };
    for body in [
        "ids[..ids.len()].len()",
        "ids[0..ids.len()].len()",
        "ids[..=ids.len() - 1].len()",
        "ids[..count()].len()",
    ] {
        let g = crate_with(body);
        assert_eq!(edges(&g), ["am.rs -> t.rs", "user.rs -> t.rs"], "{body}");
        assert_eq!(g.unknown_calls, 0, "{body}");
    }
    // A receiver the tool cannot type after `..` still imports `am.rs` through `t.rs`.
    let g = crate_with("let (y, _) = (other::make(), 0);\n    (0..y.len()).count()");
    assert_eq!(
        edges(&g),
        ["am.rs -> t.rs", "user.rs -> t.rs", "user.rs -> am.rs"]
    );
}

/// A crate of `n` types `T0` to `T{n-1}`, each in a file `t{i}.rs` with its one method `go`
/// written apart in `m{i}.rs`, which names `T{i+1}` (the last `T0`) and calls `go` on a value
/// the tool does not type: through `t{i+1}.rs`, the call imports `m{i+1}.rs`, and the `m` files
/// are one cycle of `n` files.
fn untyped_ring(n: usize) -> Vec<(String, String)> {
    let mut files = Vec::new();
    for i in 0..n {
        let next = (i + 1) % n;
        files.push((format!("t{i}.rs"), format!("pub struct T{i};\n")));
        let text = format!(
            "use crate::t{i}::T{i};\nuse crate::t{next}::T{next};\n\nimpl T{i} {{\n    \
             pub fn go(&self) -> Option<T{next}> {{\n        let z = other::make();\n        \
             z.go();\n        None\n    }}\n}}\n"
        );
        files.push((format!("m{i}.rs"), text));
    }
    let lib: String = (0..n).map(|i| format!("mod t{i};\nmod m{i};\n")).collect();
    files.push(("lib.rs".to_string(), lib));
    files.sort();
    files
}

#[test]
fn untyped_calls_scale_with_the_number_of_files() {
    // Every type has a method `go`, so each untyped call meets n type files; joined from the
    // calling file's two imports of type files, it costs two lookups, and the imports are 2n.
    let n = 200;
    let inputs = [untyped_ring(n), untyped_ring(8 * n)];
    check(
        "imports, by untyped calls of methods written apart",
        n,
        |m| {
            let files = inputs
                .iter()
                .find(|f| f.len() == 2 * m + 1)
                .expect("a size that was built");
            let g = Graph::of(files).expect("the ring's graph");
            assert_eq!(g.unknown_calls, m);
            let found = g.cycles();
            assert_eq!(found.len(), 1);
            assert_eq!(found[0].len(), m);
        },
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

#[test]
fn a_method_open_to_a_module_inside_the_calling_file_reaches_only_the_calls_in_it() {
    // `go` is open only to `user::a`, a module written inside `user.rs`, so of the two untyped
    // calls only the one in `a` may call it: the import is cited at that call's line, though the
    // other call comes first, and one call imports a file.
    let g = graph(&[
        ("lib.rs", "mod t;\nmod m;\nmod user;\n"),
        ("t.rs", "pub struct T;\n"),
        (
            "m.rs",
            "use crate::t::T;\nimpl T {\n    pub(in crate::user::a) fn go(&self) {}\n}\n",
        ),
        (
            "user.rs",
            "use crate::t::T;\npub fn f(_: &T) {\n    let z = other::make();\n    z.go();\n}\n\
             mod a {\n    pub fn g() {\n        let z = other::make();\n        z.go();\n    }\n}\n",
        ),
    ]);
    let cites: Vec<String> = g.imports[g.files.iter().position(|f| f == "user.rs").unwrap()]
        .iter()
        .map(|(t, c)| format!("{} {}:{}", g.files[*t], c.line, c.path))
        .collect();
    assert_eq!(cites, ["t.rs 1:crate::t::T", "m.rs 9:?.go"]);
    assert_eq!(g.unknown_calls, 1);
    // Open to `user` itself, the method is open to both calls, and the import is cited at the
    // first; two calls of other names on one line are cited at the earlier of them.
    let g = graph(&[
        ("lib.rs", "mod t;\nmod m;\nmod user;\n"),
        ("t.rs", "pub struct T;\n"),
        (
            "m.rs",
            "use crate::t::T;\nimpl T {\n    pub(crate) fn go(&self) {}\n    \
             pub(in crate::user) fn run(&self) {}\n}\n",
        ),
        (
            "user.rs",
            "use crate::t::T;\npub fn f(_: &T) {\n    let z = other::make();\n    \
             z.run(); z.go();\n}\nmod a {\n    pub fn g() {\n        let z = other::make();\n        \
             z.go();\n    }\n}\n",
        ),
    ]);
    let cites: Vec<String> = g.imports[g.files.iter().position(|f| f == "user.rs").unwrap()]
        .iter()
        .map(|(t, c)| format!("{} {}:{}", g.files[*t], c.line, c.path))
        .collect();
    assert_eq!(cites, ["t.rs 1:crate::t::T", "m.rs 4:?.run"]);
    assert_eq!(g.unknown_calls, 3);
    // Methods open to the crate, to `user` and to `other`, written in three files, and in
    // `m1.rs` a second one open to `user`, inside the module the first is open to: `user.rs`
    // imports `m1.rs` once and `m2.rs`, never `m3.rs`.
    let g = graph(&[
        (
            "lib.rs",
            "mod t;\nmod m1;\nmod m2;\nmod m3;\nmod other;\nmod user;\n",
        ),
        ("t.rs", "pub struct T;\npub struct U;\n"),
        (
            "m1.rs",
            "use crate::t::{T, U};\nimpl T {\n    pub(crate) fn go(&self) {}\n}\n\
             mod inner {\n    impl crate::t::U {\n        pub(in crate::user) fn go(&self) {}\n    \
             }\n}\nimpl U {\n    pub(crate) fn go(&self) {}\n}\n",
        ),
        (
            "m2.rs",
            "use crate::t::U;\nimpl U {\n    pub(in crate::user) fn go(&self) {}\n}\n",
        ),
        (
            "m3.rs",
            "use crate::t::T;\nimpl T {\n    pub(in crate::other) fn go(&self) {}\n}\n",
        ),
        ("other.rs", "pub fn f() {}\n"),
        (
            "user.rs",
            "use crate::t::T;\npub fn f(_: &T) {\n    let z = other::make();\n    z.go();\n}\n",
        ),
    ]);
    let from_user: Vec<String> = edges(&g)
        .into_iter()
        .filter(|e| e.starts_with("user.rs"))
        .collect();
    assert_eq!(
        from_user,
        ["user.rs -> t.rs", "user.rs -> m1.rs", "user.rs -> m2.rs"]
    );
    assert_eq!(g.unknown_calls, 1);
}

/// A crate of `k` types in `t.rs`, each with its method `go` written apart in `m{i}.rs`, open to
/// the crate when `open`, else to `m{i}.rs` alone, and a file `user.rs` that names `T0` and calls
/// `go` `k` times on values the tool does not type.
fn many_calls(k: usize, open: bool) -> Vec<(String, String)> {
    let vis = if open { "pub " } else { "" };
    let mut files = Vec::new();
    let types: String = (0..k).map(|i| format!("pub struct T{i};\n")).collect();
    files.push(("t.rs".to_string(), types));
    for i in 0..k {
        files.push((
            format!("m{i}.rs"),
            format!("use crate::t::T{i};\nimpl T{i} {{\n    {vis}fn go(&self) {{}}\n}}\n"),
        ));
    }
    let calls: String = (0..k).map(|_| "    z.go();\n").collect();
    files.push((
        "user.rs".to_string(),
        format!("use crate::t::T0;\npub fn f(_: &T0) {{\n    let z = other::make();\n{calls}}}\n"),
    ));
    let lib: String = std::iter::once("mod t;\nmod user;\n".to_string())
        .chain((0..k).map(|i| format!("mod m{i};\n")))
        .collect();
    files.push(("lib.rs".to_string(), lib));
    files.sort();
    files
}

/// A crate of `k` types in `t.rs`, each with a private method `go` written apart in its own
/// module `h{i}` inside `m.rs`, and a file `user.rs` that names `T0` and calls `go` `k` times on
/// values the tool does not type, none of which may call any of them.
fn many_hidden(k: usize) -> Vec<(String, String)> {
    let types: String = (0..k).map(|i| format!("pub struct T{i};\n")).collect();
    let hidden: String = (0..k)
        .map(|i| format!("mod h{i} {{\n    use crate::t::T{i};\n    impl T{i} {{\n        fn go(&self) {{}}\n    }}\n}}\n"))
        .collect();
    let calls: String = (0..k).map(|_| "    z.go();\n").collect();
    let mut files = vec![
        (
            "lib.rs".to_string(),
            "mod t;\nmod m;\nmod user;\n".to_string(),
        ),
        ("m.rs".to_string(), hidden),
        ("t.rs".to_string(), types),
        (
            "user.rs".to_string(),
            format!(
                "use crate::t::T0;\npub fn f(_: &T0) {{\n    let z = other::make();\n{calls}}}\n"
            ),
        ),
    ];
    files.sort();
    files
}

#[test]
fn many_calls_of_a_name_cost_no_more_than_their_methods() {
    // k calls of `go` in one file meet k methods of `go` through `t.rs`. Taken once for the pair
    // of file and name, they cost O(k log k), not one walk over the k methods per call (k^2),
    // whether the methods are open to the calls or not.
    let n = 200;
    let inputs = [many_calls(n, true), many_calls(8 * n, true)];
    check("imports, by many untyped calls of one name", n, |m| {
        let files = inputs
            .iter()
            .find(|f| f.len() == m + 3)
            .expect("a size that was built");
        let g = Graph::of(files).expect("the crate's graph");
        assert_eq!(g.unknown_calls, m);
        assert_eq!(g.imports.iter().map(Vec::len).sum::<usize>(), 2 * m + 1);
    });
    // Each hidden method costs the k^2 walk one check of a range, cheap beside reading its
    // lines, so the walk shows in the ratio only from k = 600 on (14.1 times at 600 and 4800).
    let n = 600;
    let inputs = [many_hidden(n), many_hidden(8 * n)];
    check("imports, by many untyped calls of hidden methods", n, |m| {
        let g = Graph::of(&inputs[usize::from(m != n)]).expect("the crate's graph");
        assert_eq!(g.unknown_calls, 0);
    });
    // Private methods in files of their own: no import either.
    let g = Graph::of(&many_calls(3, false)).expect("the crate's graph");
    assert_eq!(g.unknown_calls, 0);
}

/// A crate of `s` files `c{i}.rs` that each import the `s` files `d{k}.rs` and call each of `s`
/// methods `n{j}` on a value the tool does not type, and of `s` types `E{k}`, in `e{k}.rs`, each
/// with all the methods `n{j}`, written apart in `e.rs`. No file of a type with a method `n{j}`
/// is imported by a caller, so no call imports a file (the graph of callers, type files and names
/// has no triangle), but each of the `s^2` pairs of caller and name meets `s` type files on each
/// side of the join: `s^3` = `n^1.5` steps for an input of `n` = `s^2` lines.
fn no_triangle(s: usize) -> Vec<(String, String)> {
    let mut files = Vec::new();
    let uses: String = (0..s)
        .map(|k| format!("use crate::d{k}::D{k};\n"))
        .collect();
    let calls: String = (0..s).map(|j| format!("    z.n{j}();\n")).collect();
    for i in 0..s {
        files.push((
            format!("c{i}.rs"),
            format!("{uses}pub fn f(_: &D0) {{\n    let z = other::make();\n{calls}}}\n"),
        ));
        files.push((format!("d{i}.rs"), format!("pub struct D{i};\n")));
        files.push((format!("e{i}.rs"), format!("pub struct E{i};\n")));
    }
    let methods: String = (0..s)
        .map(|j| format!("    pub fn n{j}(&self) {{}}\n"))
        .collect();
    let impls: String = (0..s)
        .map(|k| format!("impl crate::e{k}::E{k} {{\n{methods}}}\n"))
        .collect();
    files.push(("e.rs".to_string(), impls));
    let lib: String = std::iter::once("mod e;\n".to_string())
        .chain((0..s).map(|i| format!("mod c{i};\nmod d{i};\nmod e{i};\n")))
        .collect();
    files.push(("lib.rs".to_string(), lib));
    files.sort();
    files
}

#[test]
fn untyped_calls_without_a_triangle_scale_at_the_proven_bound() {
    // The join of the pairs of caller and name with the type files costs p √p for p pairs,
    // imports and type files, and no method is near-linear unless triangles can be found in
    // near-linear time (COMPLEXITY.md F103). At `s` and `8s` the input grows 64 times and the
    // work by at most 8^3 = 512, held to n^3 log n in `s`, that is n^1.5 log n in the input.
    let s = 24;
    let inputs = [no_triangle(s), no_triangle(8 * s)];
    check_order("imports, by untyped calls with no triangle", s, 3, |m| {
        let files = inputs
            .iter()
            .find(|f| f.len() == 3 * m + 2)
            .expect("a size that was built");
        let g = Graph::of(files).expect("the crate's graph");
        assert_eq!(g.unknown_calls, 0);
        assert_eq!(g.imports.iter().map(Vec::len).sum::<usize>(), m * m + m);
    });
}
