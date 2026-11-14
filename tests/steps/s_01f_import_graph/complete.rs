//! The cases COMPLETENESS.md lists that the other tests of this group leave out: each line of
//! the report, the tool's argument errors, the lexer's raw identifiers and text cut off at the
//! end of a file, and a file read whole at every length.

use zed_tools::imports::{self, Graph};

use zed_tests::step_helpers::m0_03_grammar_tools::{Dir, tool};

use super::{edges, graph};

#[test]
fn the_report_names_each_kind_of_file_and_call_it_leaves_out() {
    // `old.rs` no `mod` reaches; `shared` a `#[path]` attribute places; `y.m()` has a receiver
    // the tool cannot type, so it imports `am.rs` through `t.rs`; and `impl Missing` names a
    // type no file defines.
    let dir = Dir::new("s1f_report_lines");
    dir.write(
        "lib.rs",
        "mod t;\nmod am;\nmod user;\n#[path = \"../shared.rs\"]\nmod shared;\n",
    );
    dir.write(
        "t.rs",
        "pub struct A;\nimpl Missing {\n    pub fn z(&self) {}\n}\n",
    );
    dir.write(
        "am.rs",
        "use crate::t::A;\nimpl A {\n    pub fn m(&self) {}\n}\n",
    );
    dir.write(
        "user.rs",
        "pub fn h(_: &crate::t::A) {}\npub fn g() { let y = other::make(); y.m(); }\n",
    );
    dir.write("old.rs", "use crate::t::A;\n");
    let (outcome, out) = tool(imports::run, &[&dir.root()]);
    assert_eq!(outcome, Ok(true), "{out}");
    let expected = format!(
        "{}: 4 files, 3 imports between files\n\
         1 .rs files no mod declaration reaches, left out\n\
         modules a #[path] attribute places, not read: lib.rs:5\n\
         1 calls of a method written apart from its type, receiver not typed, imported \
         through the type's file\n\
         1 impl blocks whose type is not found\n\
         no import cycle\n",
        dir.root()
    );
    assert_eq!(out, expected);
}

#[test]
fn the_tool_needs_a_directory_it_can_read() {
    let (outcome, out) = tool(imports::run, &[]);
    assert!(
        matches!(&outcome, Err(e) if e.contains("imports SRC_DIR…")),
        "{outcome:?} {out}"
    );
    let dir = Dir::new("s1f_no_such_dir");
    let gone = format!("{}/gone", dir.root());
    let (outcome, _) = tool(imports::run, &[&gone]);
    assert!(
        matches!(&outcome, Err(e) if e.starts_with(&format!("{gone}: "))),
        "{outcome:?}"
    );
}

#[test]
fn a_raw_identifier_is_a_name_and_not_its_keyword() {
    let g = graph(&[
        ("lib.rs", "mod a;\nmod b;\n"),
        ("a.rs", "pub fn r#type() {}\n"),
        (
            "b.rs",
            "use crate::a::r#type;\nfn f() { let r#match = 1; let _ = r#match; r#type(); }\n",
        ),
    ]);
    assert_eq!(edges(&g), ["b.rs -> a.rs"]);
}

#[test]
fn text_cut_off_at_the_end_of_a_file_names_nothing() {
    // A string never closed, and a quote that is the file's last byte, end the file; the path
    // inside the string is no import, the one before it is.
    for tail in [
        "const S: &str = \"crate::c::C",
        "const S: &str = r#\"crate::c::C\"",
        "const C: char = '",
        "const C: char = '\\",
    ] {
        let g = graph(&[
            ("lib.rs", "mod a;\nmod b;\nmod c;\n"),
            ("a.rs", "pub struct A;\n"),
            ("b.rs", &format!("use crate::a::A;\n{tail}")),
            ("c.rs", "pub struct C;\n"),
        ]);
        assert_eq!(edges(&g), ["b.rs -> a.rs"], "{tail}");
    }
}

#[test]
fn a_file_cut_off_at_every_length_is_read_without_failing() {
    // Each prefix of a file using every form the scan reads ends that form early: inside a
    // generic list, an `impl` or `fn` header, a pattern, a closure, a `for` or `match`, a path.
    // The tool reads what is there and draws only imports of what it has read.
    let full = "use crate::t::{A, Pair};\n\
        impl<T: Clone> Pair<T> {\n    pub fn get(&self) -> Option<&T> { None }\n}\n\
        pub fn f(xs: &[(u32, A)], p: Pair<A>) -> Vec<A> {\n\
        \x20   let (_, a) = &xs[0];\n\x20   a.m();\n\
        \x20   let Pair { x: b, .. } = p;\n\x20   b.m();\n\
        \x20   for (i, (_, a)) in xs.iter().enumerate() { let _ = i; a.m(); }\n\
        \x20   xs.iter().for_each(|(_, a)| a.m());\n\
        \x20   match xs.first() { Some((_, a)) => a.m(), None => {} }\n\
        \x20   let v: Vec<A> = Vec::<A>::new();\n\x20   v\n}\n";
    let files = |user: &str| {
        let files: Vec<(String, String)> = [
            ("lib.rs", "mod t;\nmod am;\nmod user;\n"),
            ("t.rs", "pub struct A;\npub struct Pair<T> { pub x: T }\n"),
            (
                "am.rs",
                "use crate::t::A;\nimpl A {\n    pub fn m(&self) {}\n}\n",
            ),
            ("user.rs", user),
        ]
        .iter()
        .map(|&(p, t)| (p.to_string(), t.to_string()))
        .collect();
        Graph::of(&files).expect("a crate whose `mod` declarations name files")
    };
    let whole = files(full);
    assert_eq!(
        edges(&whole),
        ["am.rs -> t.rs", "user.rs -> t.rs", "user.rs -> am.rs"]
    );
    for (n, _) in full.char_indices() {
        let g = files(&full[..n]);
        for e in edges(&g) {
            assert!(edges(&whole).contains(&e), "{e} at length {n}");
        }
    }
}
