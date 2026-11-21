//! FMT-comment-width-100: no `//`, `///` or `//!` comment line of a Rust file git tracks is
//! over 100 characters, the width rustfmt gives code (rustfmt.toml max_width), unless it cannot
//! be broken: its text after the marker is one token with no space (a long test path or URL),
//! it is a Markdown table row (a line of a table must stay one line), or it lies inside a ```
//! fence (an example whose lines are code). rustfmt's own comment_width
//! and wrap_comments would do this, but both are unstable options, which the pinned toolchain's
//! stable rustfmt.toml cannot use, so this test checks it. vendor/ holds code of other projects,
//! kept as they wrote it, and is not checked. Width is in characters (Unicode scalar values),
//! as `LC_ALL=C.UTF-8 awk length` counts them; the count of 2026-11-20 used that.

use std::process::Command;

use zed_tests::steps_dir;

/// The text of a comment line after its marker (`//`, `///` or `//!`) and one space, or None
/// when the line, less its leading spaces and tabs, is not a comment. O(length).
fn comment_text(line: &str) -> Option<&str> {
    let rest = line.trim_start_matches([' ', '\t']).strip_prefix("//")?;
    let rest = rest
        .strip_prefix('/')
        .or_else(|| rest.strip_prefix('!'))
        .unwrap_or(rest);
    Some(rest.strip_prefix(' ').unwrap_or(rest))
}

/// Whether comment text `t` can be broken at a space: it has a space after its indent and its
/// list marker (`-`, `*`, `+`, `1.` or `1)` and a space), outside a code span that the text is
/// made of alone (with punctuation after it). A break in the indent or after the marker alone
/// would leave a line with no words, as in `/// - \`a::long::test_path\`:`, and the rewrap keeps
/// each code span whole, so one longer than a line stays on a line of its own. A text that
/// starts with `|` is a Markdown table row, which a break would split into two rows; it is never
/// breakable (zedc-presburger row_sums/classes.rs has such a table).
fn breakable(t: &str) -> bool {
    let t = t.trim_start();
    if t.starts_with('|') {
        return false;
    }
    let t = match t.split_once(' ') {
        Some((m, rest))
            if matches!(m, "-" | "*" | "+")
                || (m.len() > 1
                    && m.ends_with(['.', ')'])
                    && m[..m.len() - 1].bytes().all(|b| b.is_ascii_digit())) =>
        {
            rest.trim_start()
        }
        _ => t,
    };
    let t = t.trim_end();
    // A text that is one code span: what follows its closing backtick has no space.
    if let Some(span) = t.strip_prefix('`')
        && let Some(end) = span.find('`')
    {
        return span[end + 1..].contains(' ');
    }
    t.contains(' ')
}

/// The 1-based numbers of the comment lines of `text` over 100 characters that could be broken
/// ([`breakable`]) and lie outside a ``` fence. A comment line whose text starts with ``` opens
/// or closes a fence. One pass over the text.
fn over_width(text: &str) -> Vec<usize> {
    let mut out = Vec::new();
    let mut fence = false;
    for (i, line) in text.lines().enumerate() {
        let Some(t) = comment_text(line) else {
            continue;
        };
        if t.starts_with("```") {
            fence = !fence;
            continue;
        }
        if !fence && breakable(t) && line.chars().count() > 100 {
            out.push(i + 1);
        }
    }
    out
}

#[test]
fn over_width_finds_breakable_comment_lines_only() {
    let long = "x".repeat(97);
    let words = format!("// {} {}", "a".repeat(50), "b".repeat(50));
    let text = format!(
        "// {long}\n{words}\n    /// {long} y\n//! {long}\n```\n// ```\n{words}\n// ```\n\
         let s = \"{long} {long}\"; // short\n//{long}zzzz\n"
    );
    // Line 1 is 100 characters; line 2 has a space; line 3 is a doc comment with a space; line 4
    // has none; line 7 lies in a fence opened by line 6 (a ``` outside a comment opens none);
    // line 9 is code; line 10 has no space after its marker.
    assert_eq!(over_width(&text), [2, 3]);
    assert_eq!(comment_text("let x = 1; // y"), None);
    assert_eq!(comment_text("\t//! a"), Some("a"));
    assert_eq!(comment_text("//no space"), Some("no space"));
    // A list item or its continuation whose words are one token cannot be broken; one of two
    // words can.
    assert!(!breakable("- `a::b`:"));
    assert!(!breakable("  `a::b`. "));
    assert!(!breakable("12) `a::b`"));
    assert!(breakable("- `a::b` and"));
    assert!(breakable("-x y"));
    // A code span with spaces inside is kept whole; a word after it can be broken off.
    assert!(!breakable("`f(a) = { b; c }`"));
    assert!(!breakable("- `f(a) = { b; c }`,"));
    assert!(breakable("`f(a) = b` and"));
    assert!(breakable("`f a"));
    // A Markdown table row is never broken, though it has spaces; a `|` later in a text is a word.
    assert!(!breakable("| a | b |"));
    assert!(!breakable("  | a | b"));
    assert!(breakable("a | b"));
    // A character outside ASCII counts once, not by its bytes: this line is 100 characters and
    // 149 bytes.
    assert_eq!(
        over_width(&format!("// {}é", "é ".repeat(48))),
        [] as [usize; 0]
    );
}

#[test]
fn no_breakable_comment_line_is_over_100_characters() {
    let root = steps_dir().join("../..");
    let listed = Command::new("git")
        .arg("-C")
        .arg(&root)
        .args(["ls-files", "-z", "--", "*.rs"])
        .output()
        .expect("git ls-files runs");
    assert!(
        listed.status.success(),
        "git ls-files: {}",
        String::from_utf8_lossy(&listed.stderr)
    );
    let paths = String::from_utf8(listed.stdout).expect("git prints UTF-8 paths");
    let mut bad = Vec::new();
    for path in paths
        .split('\0')
        .filter(|p| !p.is_empty() && !p.starts_with("vendor/"))
    {
        // A file deleted in the working tree and not yet committed has no lines.
        let Ok(text) = std::fs::read_to_string(root.join(path)) else {
            continue;
        };
        for n in over_width(&text) {
            bad.push(format!("{path}:{n}"));
        }
    }
    assert!(
        bad.is_empty(),
        "{} comment lines are over 100 characters; break each at a space, keeping its words, \
         the line's indent and marker:\n{}",
        bad.len(),
        bad.join("\n")
    );
}
