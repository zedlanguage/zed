//! The keywords and every name the prelude declares are printable ASCII, U+0021 to U+007E
//! (DESIGN.md sec:lexical; plan row NAME-ascii-library): a program's own names may be Unicode,
//! but the words every program is given can be typed on any keyboard. The tool `ascii_names`
//! checks the same of a standard library checkout (libzed); a planted `π` and `#café` show that
//! it reports what it should.

use zed_tests::step_helpers::m0_03_grammar_tools::{Dir, tool};
use zed_tools::ascii_names::{is_printable_ascii, non_ascii_names, run};
use zedc::lex::KEYWORDS;
use zedc::resolve::{ANNOTATIONS, LATER_TYPES, TYPES, WORDS};

#[test]
fn every_keyword_is_printable_ascii() {
    for k in KEYWORDS {
        assert!(is_printable_ascii(k), "{k:?}");
    }
}

#[test]
fn every_word_type_and_annotation_the_resolver_gives_the_prelude_is_printable_ascii() {
    let names = WORDS
        .iter()
        .chain(LATER_TYPES)
        .chain(ANNOTATIONS)
        .map(|&(w, _)| w)
        .chain(TYPES.iter().copied());
    for w in names {
        assert!(is_printable_ascii(w), "{w:?}");
    }
}

#[test]
fn every_name_in_the_prelude_source_is_printable_ascii() {
    let prelude = format!("{}/zed/prelude", zed_tools::impl_root());
    let files = std::fs::read_dir(&prelude)
        .expect("the prelude directory")
        .filter(|e| {
            e.as_ref()
                .is_ok_and(|e| e.path().extension().is_some_and(|x| x == "zed"))
        })
        .count();
    assert!(files >= 7, "{files} prelude files in {prelude}");
    assert_eq!(tool(run, &[&prelude]), (Ok(true), String::new()));
}

#[test]
fn a_non_ascii_name_atom_or_annotation_in_code_is_reported_and_text_is_not() {
    let text = "// π, #café and @größe in a comment are text.\n\
                π = 3.14;\n\
                s = \"π ${ä} π\";\n\
                @größe f() -> int { #café }\n";
    assert_eq!(
        non_ascii_names(text),
        Ok(vec![
            (2, 1, "π".to_string()),
            (3, 10, "ä".to_string()),
            (4, 1, "@größe".to_string()),
            (4, 21, "#café".to_string()),
        ])
    );
    assert_eq!(non_ascii_names("x = 1; // π\n#ok;"), Ok(vec![]));
}

#[test]
fn the_tool_reports_each_planted_name_and_skips_hidden_directories() {
    let dir = Dir::new("ascii_names");
    let root = dir.root();
    for d in ["lib", "lib/geo", ".git"] {
        std::fs::create_dir_all(format!("{root}/{d}")).expect("a test directory");
    }
    dir.write("lib/a.zed", "x = 1; // π\n");
    dir.write("lib/geo/pi.zed", "π = 3.14;\nf() -> int { #café }\n");
    dir.write("lib/geo/notes.txt", "π = 3.14;\n");
    dir.write(".git/b.zed", "π = 3.14;\n");
    dir.write("lib/bad.zed", "x = \u{200d};\n");
    let (outcome, out) = tool(run, &[&root]);
    let at = |f: &str| format!("{root}/{f}");
    assert_eq!(outcome, Ok(false));
    assert_eq!(
        out,
        format!(
            "{} FAIL {}\n{}:1:1: the name `π`\n{}:2:14: the name `#café`\n",
            at("lib/bad.zed"),
            zedc::lex::lex("x = \u{200d};\n").unwrap_err(),
            at("lib/geo/pi.zed"),
            at("lib/geo/pi.zed"),
        )
    );
    // Without the planted names the same checkout passes.
    dir.write("lib/geo/pi.zed", "pi = 3.14;\nf() -> int { #cafe }\n");
    dir.write("lib/bad.zed", "x = 1;\n");
    assert_eq!(tool(run, &[&root]), (Ok(true), String::new()));
}
