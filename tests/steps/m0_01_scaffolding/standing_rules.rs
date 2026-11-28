//! TOOLS-mechanical-rule-checks: the standing code rules that are a pattern in the source,
//! checked over every file git tracks (vendor/ holds other projects' code as they wrote it and is
//! not checked), each with a negative control on text written here. The rules:
//! - no ignored test: no `#[ignore]` attribute (author 2026-11-13, P149, P150: fix the code or
//!   the test; a test that waits for a later step is kept in that step's deferred-tests file);
//! - no Python: no `.py`, `.pyw` or `.pyc` file and no `#!` line naming python (author
//!   2026-10-31; the repository holds Rust, Zed and the TypeScript of tools/dagview);
//! - no "golden" for a test's expected output (author 2026-10-31: say "expected output"), in
//!   any file name or in a `.rs`, `.zed`, `.sh` or `.ts` file; "golden ratio" and the cited
//!   constant `GOLDEN_GAMMA` (zed-hash, Steele, Lea and Flood 2014) are other words and pass;
//! - no identifier `cum` (author 2026-10-29: it reads as a vulgar word; `cumul`, `running`,
//!   `prefix`), as a whole word or a part of a snake_case or camelCase name in a `.rs`, `.zed` or
//!   `.sh` file;
//! - a float test is written with a dot and no parentheses, `x.isFinite` (author 2026-11-21):
//!   no `isFinite()`, `isNaN()`, `isInfinite()` and no `::` before those names, in a `.rs`,
//!   `.zed` or `.md` file other than the plan (docs/plan_dag.md quotes the forms refused);
//! - no session line of the assistant that wrote a change (the author's standing order: no
//!   session id or session link in commits, code or docs) in any text file.
//! The ASCII rule for names is checked by the lexer itself (l01_02_lexer_names/ascii.rs). No
//! standing rule names a method or a type to refuse, which is what clippy's disallowed-methods
//! and disallowed-types check, so clippy.toml gains none. Rules that need the structure of the
//! code, not a pattern (a copy made only for the borrow checker, a magic constant without its
//! comment, a closure search without a visited set, a hash map's order reaching an output), are
//! left to DECIDE-ast-grep-dependency. This file writes the refused forms in its controls, so it
//! is not itself scanned. Cost: one pass over each tracked file's text, O(total size).

use std::process::Command;

use zed_tests::steps_dir;

/// This file, which holds every refused form in its controls.
const SELF: &str = "tests/steps/m0_01_scaffolding/standing_rules.rs";

/// The 1-based lines of `text` that are an `#[ignore]` attribute, alone or with a reason.
fn ignored(text: &str) -> Vec<usize> {
    lines_where(text, |l| {
        let l = l.trim_start();
        l.starts_with("#[ignore]") || l.starts_with("#[ignore =") || l.starts_with("#[ignore(")
    })
}

/// Whether a file at `path` with text `text` is Python: by its extension, or by a first line
/// `#!` that names python.
fn python(path: &str, text: &str) -> bool {
    [".py", ".pyw", ".pyc"].iter().any(|x| path.ends_with(x))
        || text
            .lines()
            .next()
            .is_some_and(|l| l.starts_with("#!") && l.contains("python"))
}

/// The 1-based lines of `text` that say "golden", in any case, other than "golden ratio" and
/// `GOLDEN_GAMMA`; line 0 stands for the file name `path`.
fn golden(path: &str, text: &str) -> Vec<usize> {
    let bad = |l: &str| {
        let l = l.to_ascii_lowercase();
        l.match_indices("golden").any(|(i, _)| {
            let after = &l[i + "golden".len()..];
            !(after.starts_with(" ratio") || after.starts_with("_gamma"))
        })
    };
    let mut out = if bad(path) { vec![0] } else { vec![] };
    out.extend(lines_where(text, bad));
    out
}

/// The 1-based lines of `text` with a word `cum`: a run of letters `cum` in any case, between
/// two characters that are not letters or digits, or at a camelCase boundary (`cumSum`,
/// `sumCum`). `cumul`, `accum` and `document` pass.
fn cum(text: &str) -> Vec<usize> {
    lines_where(text, |l| {
        let b = l.as_bytes();
        l.to_ascii_lowercase().match_indices("cum").any(|(i, _)| {
            let j = i + 3;
            let start = i == 0
                || !b[i - 1].is_ascii_alphanumeric()
                || (b[i].is_ascii_uppercase() && b[i - 1].is_ascii_lowercase());
            let end = j == b.len()
                || !b[j].is_ascii_alphanumeric()
                || (b[j].is_ascii_uppercase() && b[j - 1].is_ascii_lowercase());
            start && end
        })
    })
}

/// The 1-based lines of `text` with a float test written with parentheses or after `::`.
fn float_test(text: &str) -> Vec<usize> {
    lines_where(text, |l| {
        ["isFinite", "isNaN", "isInfinite"].iter().any(|w| {
            l.match_indices(w).any(|(i, _)| {
                let after = &l[i + w.len()..];
                let next = after.bytes().next();
                let whole = !next.is_some_and(|c| c.is_ascii_alphanumeric() || c == b'_');
                whole && (after.starts_with("()") || l[..i].ends_with("::"))
            })
        })
    })
}

/// The 1-based lines of `text` with a session trailer or a session link.
fn session(text: &str) -> Vec<usize> {
    let trailer = concat!("Claude", "-Session:");
    let link = concat!("claude", ".ai/code");
    lines_where(text, |l| l.contains(trailer) || l.contains(link))
}

/// The 1-based numbers of the lines of `text` that `bad` holds for.
fn lines_where(text: &str, bad: impl Fn(&str) -> bool) -> Vec<usize> {
    (text.lines().enumerate())
        .filter(|(_, l)| bad(l))
        .map(|(i, _)| i + 1)
        .collect()
}

#[test]
fn each_rule_finds_its_refused_form_and_passes_the_others() {
    let none: Vec<usize> = vec![];
    assert_eq!(
        ignored(
            "#[test]\n#[ignore]\nfn a() {}\n    #[ignore = \"slow\"]\n// #[ignore]\nlet s = \"#[ignore]\";\n"
        ),
        [2, 4]
    );
    assert!(python("tools/a.py", ""));
    assert!(python("tools/a", "#!/usr/bin/env python3\n"));
    assert!(!python("tools/a.sh", "#!/bin/bash\n# python is not used\n"));
    assert!(!python("tools/a.pyx.rs", "fn a() {}\n"));
    assert_eq!(
        golden(
            "tests/a.rs",
            "let golden = 1;\n// the golden ratio\nGOLDEN_GAMMA\nGolden output\n"
        ),
        [1, 4]
    );
    assert_eq!(golden("tests/golden/a.out", ""), [0]);
    assert_eq!(golden("crates/a.rs", "// φ, the golden ratio\n"), none);
    assert_eq!(
        cum(
            "let cum = 0;\nlet cumul = 0;\nfn sum_cum() {}\nlet cumSum = 1;\nlet accum = 2;\n\
             // a document\nx.CUM\nlet sumCum = 3;\nlet cum2 = 4;\n"
        ),
        [1, 3, 4, 7, 8]
    );
    assert_eq!(
        float_test(
            "x.isFinite\nx.isFinite()\nx::isNaN\nf64::is_finite(x)\nx.isNaNy()\nx.isInfinite ()\n"
        ),
        [2, 3]
    );
    let trailer = concat!("Claude", "-Session: x");
    let link = concat!("see https://claude", ".ai/code/x");
    assert_eq!(session(&format!("a\n{trailer}\n{link}\nclaude\n")), [2, 3]);
}

/// The paths of the files git tracks in the checkout, less vendor/ and this file.
fn tracked() -> Vec<String> {
    let root = steps_dir().join("../..");
    let listed = Command::new("git")
        .arg("-C")
        .arg(&root)
        .args(["ls-files", "-z"])
        .output()
        .expect("git ls-files runs");
    assert!(
        listed.status.success(),
        "git ls-files: {}",
        String::from_utf8_lossy(&listed.stderr)
    );
    let paths = String::from_utf8(listed.stdout).expect("git prints UTF-8 paths");
    (paths.split('\0'))
        .filter(|p| !p.is_empty() && !p.starts_with("vendor/") && *p != SELF)
        .map(str::to_string)
        .collect()
}

#[test]
fn no_tracked_file_breaks_a_standing_rule_that_is_a_pattern() {
    let root = steps_dir().join("../..");
    let ext = |p: &str, xs: &[&str]| xs.iter().any(|x| p.ends_with(x));
    let mut bad = Vec::new();
    let mut read = 0;
    for path in tracked() {
        let at = |what: &str, lines: Vec<usize>| -> Vec<String> {
            lines
                .into_iter()
                .map(|n| format!("{path}:{n}: {what}"))
                .collect()
        };
        // A file deleted in the working tree and not yet committed has no text; a file that is
        // not UTF-8 (an image, a profile) is checked by its name alone.
        let text = std::fs::read_to_string(root.join(&path)).unwrap_or_default();
        read += 1;
        if python(&path, &text) {
            bad.push(format!("{path}: a Python file; write it in Rust"));
        }
        let names = if ext(&path, &[".rs", ".zed", ".sh", ".ts"]) {
            golden(&path, &text)
        } else {
            golden(&path, "")
        };
        bad.extend(at("\"golden\"; say \"expected output\"", names));
        if ext(&path, &[".rs"]) {
            bad.extend(at(
                "#[ignore]; fix the code or the test, or defer it",
                ignored(&text),
            ));
        }
        if ext(&path, &[".rs", ".zed", ".sh"]) {
            bad.extend(at(
                "the name `cum`; write `cumul`, `running` or `prefix`",
                cum(&text),
            ));
        }
        if ext(&path, &[".rs", ".zed", ".md"]) && path != "docs/plan_dag.md" {
            bad.extend(at(
                "a float test with () or ::; write `x.isFinite`",
                float_test(&text),
            ));
        }
        bad.extend(at("a session line; remove it", session(&text)));
    }
    assert!(read > 1000, "{read} tracked files read");
    assert!(
        bad.is_empty(),
        "{} breaks of a standing rule:\n{}",
        bad.len(),
        bad.join("\n")
    );
}
