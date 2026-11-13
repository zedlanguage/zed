//! Characters that show as nothing or as blank space (DESIGN.md sec:lexical; QUESTIONS A97,
//! 2026-11-12): every character with the Unicode property Default_Ignorable_Code_Point (UAX
//! #31's Default Ignorable Exclusion Profile, section 7.3) and the three blank characters
//! U+13441, U+13442 and U+16FE4. A name is ASCII (NAME-ascii-only), so none is a name
//! character; each is an error in code, after a name, at its start or end, after the wildcard, a
//! number or a keyword, and in the code of a hole, with the message of a character that may not
//! show, which names it by its code point. A comment and the text of a string take it. The
//! lexer and the grammar engine both follow the rule.
//!
//! `default_ignorable.txt` and `format.txt` are the sections of Default_Ignorable_Code_Point in
//! DerivedCoreProperties.txt and of General_Category=Format in DerivedGeneralCategory.txt, of the
//! Unicode version of the lexer's tables (`zedc::lex::UNICODE_VERSION`), copied unchanged with
//! each file's header.

use std::sync::Arc;

use zed_tests::step_helpers::m0_03_grammar_tools::{design, spec_dir};
use zed_tools::spec::Spec;
use zedc::lex::{
    ErrorKind, Part, Tok, UNICODE_VERSION, is_blank, is_default_ignorable, is_format,
    is_name_continue, is_name_start, lex, may_not_show, name_end,
};

use super::invisible::invisible;

/// The section of Default_Ignorable_Code_Point in DerivedCoreProperties.txt.
const DEFAULT_IGNORABLE: &str = include_str!("default_ignorable.txt");

/// The section of General_Category=Format in DerivedGeneralCategory.txt.
const FORMAT: &str = include_str!("format.txt");

/// The characters whose glyph is blank and which lack the property Default_Ignorable_Code_Point:
/// EGYPTIAN HIEROGLYPH FULL BLANK, EGYPTIAN HIEROGLYPH HALF BLANK and KHITAN SMALL SCRIPT FILLER.
const BLANK: [char; 3] = ['\u{13441}', '\u{13442}', '\u{16FE4}'];

/// One past the last code point.
const CODE_POINTS: usize = 0x11_0000;

/// For each code point, whether `data` lists it with the value `value`. Checks the total the
/// file states.
fn listed(data: &str, value: &str) -> Vec<bool> {
    let mut listed = vec![false; CODE_POINTS];
    let mut total = None;
    for line in data.lines() {
        if let Some(t) = line.strip_prefix("# Total code points: ") {
            total = Some(t.parse::<usize>().expect("a total"));
        }
        if line.starts_with('#') || line.is_empty() {
            continue;
        }
        let (points, rest) = line.split_once(';').expect("a data line");
        assert!(
            rest.trim_start().starts_with(&format!("{value} ")),
            "{line}"
        );
        let points = points.trim();
        let (lo, hi) = points.split_once("..").unwrap_or((points, points));
        let hex = |s: &str| usize::from_str_radix(s, 16).expect("a code point");
        for flag in &mut listed[hex(lo)..=hex(hi)] {
            *flag = true;
        }
    }
    assert_eq!(
        Some(listed.iter().filter(|&&x| x).count()),
        total,
        "the total the file states"
    );
    listed
}

/// Every character other than a surrogate.
fn every_char() -> impl Iterator<Item = char> {
    (0..CODE_POINTS as u32).filter_map(char::from_u32)
}

/// The characters that show as nothing or as blank space, in order, by the data file.
fn blank() -> Vec<char> {
    let listed = listed(DEFAULT_IGNORABLE, "Default_Ignorable_Code_Point");
    every_char()
        .filter(|&c| listed[c as usize] || BLANK.contains(&c))
        .collect()
}

/// The code points `wrong` holds, for a message: how many and the first twenty.
fn show(wrong: &[char]) -> String {
    let first: Vec<String> = wrong
        .iter()
        .take(20)
        .map(|&c| format!("U+{:04X}", c as u32))
        .collect();
    format!("{} code points, the first {first:?}", wrong.len())
}

#[test]
fn the_data_files_are_of_the_unicode_version_of_the_lexer_tables() {
    let (major, minor, update) = UNICODE_VERSION;
    for (data, file) in [
        (DEFAULT_IGNORABLE, "DerivedCoreProperties"),
        (FORMAT, "DerivedGeneralCategory"),
    ] {
        assert_eq!(
            data.lines().next(),
            Some(format!("# {file}-{major}.{minor}.{update}.txt").as_str())
        );
    }
}

#[test]
fn the_blank_characters_are_the_default_ignorable_code_points_and_three_more() {
    let listed = listed(DEFAULT_IGNORABLE, "Default_Ignorable_Code_Point");
    let wrong: Vec<char> = every_char()
        .filter(|&c| is_default_ignorable(c) != listed[c as usize])
        .collect();
    assert!(
        wrong.is_empty(),
        "differ from the data file: {}",
        show(&wrong)
    );
    let others: Vec<char> = every_char()
        .filter(|&c| is_blank(c) && !is_default_ignorable(c))
        .collect();
    assert_eq!(others, BLANK);
}

#[test]
fn the_format_table_is_the_general_category_cf() {
    let listed = listed(FORMAT, "Cf");
    let wrong: Vec<char> = every_char()
        .filter(|&c| is_format(c) != listed[c as usize])
        .collect();
    assert!(
        wrong.is_empty(),
        "differ from the data file: {}",
        show(&wrong)
    );
}

#[test]
fn a_name_takes_exactly_the_ascii_name_characters() {
    for c in every_char() {
        assert_eq!(is_name_start(c), c.is_ascii_alphabetic(), "{c:?}");
        assert_eq!(
            is_name_continue(c),
            c.is_ascii_alphanumeric() || c == '_',
            "{c:?}"
        );
        // After `a`, a name takes `c` exactly when `c` continues a name; `'` ends one.
        let end = match c {
            _ if is_name_continue(c) => 1 + c.len_utf8(),
            '\'' => 2,
            _ => 1,
        };
        assert_eq!(name_end(&format!("a{c}"), 0), Some(end), "{c:?}");
        // A name starts with `c` exactly when `c` starts a name, or is `_` before a letter.
        let start = (is_name_start(c) || c == '_').then_some(c.len_utf8() + 1);
        assert_eq!(name_end(&format!("{c}a"), 0), start, "{c:?}");
    }
}

#[test]
fn each_blank_character_is_an_error_where_code_would_take_it() {
    for c in blank() {
        let hex = format!("{:X}", c as u32);
        let width = c.len_utf8();
        for (text, at) in [
            (format!("a{c}b = 1;"), 1),
            (format!("a = {c}b;"), 4),
            (format!("ab{c} = 1;"), 2),
            (format!("a = _{c};"), 5),
            (format!("a = 1{c};"), 5),
            (format!("if{c}x"), 2),
            (format!("a = \"${{b{c}c}}\";"), 8),
        ] {
            let e = lex(&text).expect_err(&text);
            let message = e.to_string();
            assert_eq!(
                (e.kind, (e.span.start, e.span.end), &message),
                (ErrorKind::Unexpected(c), (at, at + width), &invisible(&hex)),
                "{text:?}"
            );
            assert!(!message.contains(c), "{text:?}");
        }
    }
}

#[test]
fn a_hangul_filler_or_an_egyptian_blank_at_the_start_of_a_name_is_named_by_its_code_point() {
    // Each takes one or two columns and shows as blank space, so the message must not print it.
    for (c, hex) in [
        ('\u{3164}', "3164"),
        ('\u{FFA0}', "FFA0"),
        ('\u{115F}', "115F"),
        ('\u{13441}', "13441"),
        ('\u{13442}', "13442"),
    ] {
        let text = format!("{c}b = 1;");
        let e = lex(&text).expect_err(&text);
        let message = e.to_string();
        assert_eq!(
            (e.kind, (e.span.start, e.span.end), &message),
            (ErrorKind::Unexpected(c), (0, c.len_utf8()), &invisible(hex)),
            "{text:?}"
        );
        assert!(!message.contains(c), "{text:?}");
    }
}

#[test]
fn a_message_names_a_character_that_may_not_show_by_its_code_point() {
    // A control, a format character, spaces, separators, a private-use character, an unassigned
    // code point, a noncharacter, a Hangul filler and the three blanks.
    for c in [
        '\u{1B}',
        '\u{600}',
        '\u{FFF9}',
        '\u{A0}',
        '\u{3000}',
        '\u{2028}',
        '\u{2029}',
        '\u{E000}',
        '\u{10FFFD}',
        '\u{378}',
        '\u{FFFF}',
        '\u{3164}',
        '\u{13441}',
        '\u{13442}',
        '\u{16FE4}',
    ] {
        assert!(may_not_show(c), "U+{:04X}", c as u32);
    }
    // Letters, a wide character, an emoji and visible symbols that start no token.
    for c in [
        'a',
        '\u{E9}',
        '\u{65E5}',
        '\u{1F600}',
        '\u{20AC}',
        '$',
        '\u{B6}',
    ] {
        assert!(!may_not_show(c), "U+{:04X}", c as u32);
    }
    // A visible character that starts no token is quoted as itself.
    let e = lex("a = 1 \u{20AC};").expect_err("the euro sign");
    assert!(
        e.to_string()
            .starts_with("the character `\u{20AC}` (U+20AC)")
    );
    // An unassigned code point is named by its code point.
    let e = lex("a = 1 \u{378};").expect_err("U+0378");
    assert_eq!(e.to_string(), invisible("378"));
}

#[test]
fn each_blank_character_is_taken_in_a_comment_and_in_string_text() {
    for c in blank() {
        for text in [
            format!("a = 1; // {c} x\n"),
            format!("/* {c} */ a = 1;"),
            format!("a = \"${{b}}{c}\";"),
        ] {
            assert!(lex(&text).is_ok(), "{text:?}: {}", lex(&text).unwrap_err());
        }
        let text = format!("a = \"x{c}y\";");
        let tokens = lex(&text).unwrap_or_else(|e| panic!("{text:?}: {e}"));
        assert_eq!(
            tokens[2].tok,
            Tok::Str(vec![Part::Text(Arc::new(format!("x{c}y")))]),
            "{text:?}"
        );
    }
}

#[test]
fn the_grammar_engine_rejects_each_blank_character_in_code_and_takes_it_elsewhere() {
    let dir = spec_dir("default_ignorable", &design(""), "");
    let spec = Spec::open(&dir.root()).expect("the spec reads");
    let engine = |text: &str| zed_tools::syntax::lex(&spec.lexical, text);
    // Without a blank character each of these is read.
    for text in [
        "ab = 1;",
        "a = b;",
        "a = _;",
        "a = 1;",
        "if x",
        "a = \"x\";",
    ] {
        assert!(engine(text).is_ok(), "{text:?}");
    }
    for c in blank() {
        for text in [
            format!("a{c}b = 1;"),
            format!("a = {c}b;"),
            format!("a = _{c};"),
            format!("a = 1{c};"),
            format!("if{c}x"),
        ] {
            assert!(engine(&text).is_err(), "{text:?}");
        }
        for text in [format!("a = 1; // {c} x\n"), format!("a = \"x{c}y\";")] {
            assert!(
                engine(&text).is_ok(),
                "{text:?}: {}",
                engine(&text).unwrap_err()
            );
        }
    }
}
