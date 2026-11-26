//! TEST-runtime-panic-guard: every place in the code a built executable runs that panics when
//! its condition fails carries a comment saying why the condition holds. A site is `panic!`,
//! `unreachable!`, `todo!` or `unimplemented!`; `.unwrap()`, `.expect(…)`, `.unwrap_err()` or
//! `.expect_err(…)`; or an index `a[i]` or a slice `a[i..j]` (the whole slice `a[..]` cannot
//! panic and is not one). The comment is `// Cannot panic: <why>`, on its own line before the
//! code, its reason going on over the `//` lines after it, or at the end of the site's own
//! line. A comment on its own line covers the code lines after it up to a blank line, a
//! comment line, or a line indented less than the first it covers. A comment that covers no
//! site fails too, so that none outlives its site.
//!
//! The code a built executable runs: the crate zed-rt, and the modules of zed-native its start
//! (`exe::zed_main`) reaches: `exe` (the program decoded), `legal` (its graph legalized again),
//! `tables` (built from the graph), `outcome` and `hooks` (the run) and `bug`. The other
//! modules of zed-native (`codegen`, `dwarf`, `link`, `section`, `sources` and `lib.rs`) run in
//! the compiler and are not read here. Each crate is read as its module tree from its root,
//! following `mod name;` and `include!`, and an item under `#[cfg(test)]` (a test module, a
//! file of tests) is left out: a panic there is a failed test.
//!
//! Not checked: `assert!` and its kin, whose panic states a broken invariant on purpose;
//! arithmetic overflow and division by zero; a `RefCell` borrowed twice; a panic inside a
//! library the runtime calls; and the code of zedc that runs at the start (the decoder and
//! validator of the graph, the plan's reader), which lives in zedc's crates.
//!
//! A panic in a built executable reaches its panic hook (`exe::start`), which reports a bug in
//! zedc and ends the run with status 3. A site that a well-formed or a damaged executable can
//! make fire is a fault, fixed to give an error; the comment is for a site that cannot fire.
//!
//! The reading is a small lexer of Rust, enough for this code: line and nested block comments,
//! strings with escapes, raw strings, and character literals told from lifetimes. O(n) in the
//! size of the files read.

use std::fs;
use std::path::{Path, PathBuf};

use zed_tests::steps_dir;

/// The marker a reason starts with.
const MARKER: &str = "// Cannot panic:";

/// One line of a Rust file as [`lex`] reads it.
#[derive(Default, Debug)]
struct Line {
    /// The code, with comments left out and each string and character literal emptied (its
    /// quotes kept), so that nothing inside a literal reads as code.
    code: String,
    /// The `//` comment at the end of the line, from its `//`.
    comment: Option<String>,
    /// Whether the line starts inside a string literal, so that its code goes on from the line
    /// before whatever its indent.
    in_string: bool,
}

/// Whether `c` can be part of an identifier.
fn ident(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

/// The lines of `text`, one for each of its lines. O(length).
fn lex(text: &str) -> Vec<Line> {
    enum St {
        Code,
        /// A block comment, nested this deep.
        Block(usize),
        Str,
        /// A raw string closed by `"` and this many `#`.
        Raw(usize),
    }
    let cs: Vec<char> = text.chars().collect();
    let mut lines = vec![Line::default()];
    let mut st = St::Code;
    let mut i = 0;
    while i < cs.len() {
        let c = cs[i];
        let next = cs.get(i + 1).copied();
        if c == '\n' {
            lines.push(Line {
                in_string: matches!(st, St::Str | St::Raw(_)),
                ..Line::default()
            });
            i += 1;
            continue;
        }
        let line = lines.last_mut().expect("one line at least");
        match st {
            St::Block(d) => {
                if c == '*' && next == Some('/') {
                    st = if d == 1 { St::Code } else { St::Block(d - 1) };
                    i += 2;
                } else if c == '/' && next == Some('*') {
                    st = St::Block(d + 1);
                    i += 2;
                } else {
                    i += 1;
                }
            }
            St::Str => {
                if c == '\\' {
                    // An escaped line break is read as a line break next.
                    i += if next == Some('\n') { 1 } else { 2 };
                } else {
                    if c == '"' {
                        line.code.push('"');
                        st = St::Code;
                    }
                    i += 1;
                }
            }
            St::Raw(h) => {
                let closes = c == '"' && (1..=h).all(|k| cs.get(i + k) == Some(&'#'));
                if closes {
                    line.code.push('"');
                    st = St::Code;
                    i += 1 + h;
                } else {
                    i += 1;
                }
            }
            St::Code => {
                let prev = if i > 0 { cs[i - 1] } else { ' ' };
                if c == '/' && next == Some('/') {
                    let end = cs[i..]
                        .iter()
                        .position(|&x| x == '\n')
                        .map_or(cs.len(), |k| i + k);
                    line.comment = Some(cs[i..end].iter().collect());
                    i = end;
                } else if c == '/' && next == Some('*') {
                    st = St::Block(1);
                    i += 2;
                } else if c == '"' {
                    line.code.push('"');
                    st = St::Str;
                    i += 1;
                } else if c == 'r'
                    && (!ident(prev) || (prev == 'b' && (i < 2 || !ident(cs[i - 2]))))
                    && let Some(h) = cs[i + 1..].iter().position(|&x| x != '#')
                    && cs[i + 1 + h] == '"'
                {
                    line.code.push('"');
                    st = St::Raw(h);
                    i += h + 2;
                } else if c == '\'' && next == Some('\\') {
                    // An escaped character: its closing quote is after the escaped character.
                    let end = cs[i + 3..]
                        .iter()
                        .position(|&x| x == '\'')
                        .map_or(cs.len(), |k| i + 3 + k);
                    line.code.push_str("' '");
                    i = end + 1;
                } else if c == '\'' && cs.get(i + 2) == Some(&'\'') {
                    line.code.push_str("' '");
                    i += 3;
                } else {
                    // Any other quote starts a lifetime or a label.
                    line.code.push(c);
                    i += 1;
                }
            }
        }
    }
    lines
}

/// The kinds of site on code line `code`, in the order of the list in the head comment.
fn sites(code: &str) -> Vec<&'static str> {
    let mut found = Vec::new();
    for mac in ["panic", "unreachable", "todo", "unimplemented"] {
        let pat = format!("{mac}!");
        let at_word = code
            .match_indices(&pat)
            .any(|(i, _)| code[..i].chars().next_back().is_none_or(|p| !ident(p)));
        if at_word {
            found.push(mac);
        }
    }
    for (pat, kind) in [
        (".unwrap()", "unwrap"),
        (".expect(", "expect"),
        (".unwrap_err()", "unwrap_err"),
        (".expect_err(", "expect_err"),
    ] {
        if code.contains(pat) {
            found.push(kind);
        }
    }
    let index = code.match_indices('[').any(|(i, _)| {
        let after = code[..i].chars().next_back();
        after.is_some_and(|p| ident(p) || p == ')' || p == ']') && !code[i..].starts_with("[..]")
    });
    if index {
        found.push("index");
    }
    found
}

/// For each line, whether it is outside every item under `#[cfg(test)]`; and the names of the
/// modules of files that are declared under it (`#[cfg(test)] mod name;`).
fn live(lines: &[Line]) -> (Vec<bool>, Vec<String>) {
    let mut live = vec![true; lines.len()];
    let mut tests = Vec::new();
    let mut i = 0;
    while i < lines.len() {
        let code = lines[i].code.trim();
        if code.contains("cfg(") && code.contains("test") && code != "#[cfg(test)]" {
            panic!("`{code}`: a test condition other than `#[cfg(test)]`, which this test reads");
        }
        if code != "#[cfg(test)]" {
            i += 1;
            continue;
        }
        // The item: attributes, then a declaration ended by `;` or a braced body.
        live[i] = false;
        i += 1;
        let mut depth = 0usize;
        let mut opened = false;
        while i < lines.len() {
            live[i] = false;
            let code = lines[i].code.trim();
            let attribute = depth == 0 && !opened && code.starts_with("#[");
            if !attribute {
                for c in code.chars() {
                    match c {
                        '{' => {
                            depth += 1;
                            opened = true;
                        }
                        '}' => depth -= 1,
                        _ => {}
                    }
                }
            }
            i += 1;
            if opened && depth == 0 {
                break;
            }
            if !opened && !attribute && code.ends_with(';') {
                if let Some(name) = declared_mod(code) {
                    tests.push(name.to_string());
                }
                break;
            }
        }
    }
    (live, tests)
}

/// The name in `mod name;`, with any `pub` or `pub(…)` before it.
fn declared_mod(code: &str) -> Option<&str> {
    let rest = code.strip_prefix("pub").map_or(code, |r| {
        let r = r.trim_start();
        match r.strip_prefix('(') {
            Some(inner) => inner.split_once(')').map_or(r, |(_, after)| after),
            None => r,
        }
    });
    let name = rest
        .trim_start()
        .strip_prefix("mod ")?
        .strip_suffix(';')?
        .trim();
    name.chars().all(ident).then_some(name)
}

/// What [`check`] finds wrong in one file: each site no reason covers, with its line number
/// (from 1) and kinds, and each reason that covers no site or is empty, by line number.
#[derive(Debug, Default, PartialEq)]
struct Faults {
    bare: Vec<(usize, Vec<&'static str>)>,
    stale: Vec<usize>,
    empty: Vec<usize>,
}

/// The sites, faults and test modules of the Rust text `text`. O(length).
fn check(text: &str) -> (usize, Faults, Vec<String>) {
    let lines = lex(text);
    let (live, tests) = live(&lines);
    let raw: Vec<&str> = text.split('\n').collect();
    let indent = |k: usize| raw[k].len() - raw[k].trim_start().len();
    let is_marker = |l: &Line| l.comment.as_deref().is_some_and(|c| c.starts_with(MARKER));
    let mut covered = vec![None; lines.len()];
    let mut markers: Vec<(usize, bool)> = Vec::new();
    let mut faults = Faults::default();
    let mut i = 0;
    while i < lines.len() {
        let l = &lines[i];
        if !live[i] || !is_marker(l) {
            i += 1;
            continue;
        }
        let m = markers.len();
        markers.push((i, false));
        let mut reason = l.comment.as_deref().unwrap_or_default()[MARKER.len()..].to_string();
        if !l.code.trim().is_empty() {
            // At the end of a site's own line: that line only.
            covered[i] = Some(m);
            if reason.trim().is_empty() {
                faults.empty.push(i + 1);
            }
            i += 1;
            continue;
        }
        let mut j = i + 1;
        while j < lines.len() && lines[j].code.trim().is_empty() && !is_marker(&lines[j]) {
            match &lines[j].comment {
                Some(c) => reason.push_str(c.trim_start_matches('/')),
                None => break,
            }
            j += 1;
        }
        if reason.trim().is_empty() {
            faults.empty.push(i + 1);
        }
        let first = j;
        let mut k = first;
        while k < lines.len()
            && (lines[k].in_string
                || (!lines[k].code.trim().is_empty() && indent(k) >= indent(first)))
        {
            covered[k] = Some(m);
            k += 1;
        }
        i = j;
    }
    let mut count = 0;
    for (k, l) in lines.iter().enumerate() {
        let kinds = sites(&l.code);
        if !live[k] || kinds.is_empty() {
            continue;
        }
        count += 1;
        match covered[k] {
            Some(m) => markers[m].1 = true,
            None => faults.bare.push((k + 1, kinds)),
        }
    }
    faults.stale = markers.iter().filter(|m| !m.1).map(|m| m.0 + 1).collect();
    (count, faults, tests)
}

/// The directory that holds the modules file `f` declares.
fn module_dir(f: &Path) -> PathBuf {
    let dir = f.parent().expect("a file in a directory");
    match f.file_name().and_then(|n| n.to_str()) {
        Some("lib.rs" | "mod.rs") => dir.to_path_buf(),
        _ => dir.join(f.file_stem().expect("a file name")),
    }
}

/// The files of the module tree under `root`, each with its text, following each `mod name;`
/// and `include!` outside the items under `#[cfg(test)]`; at `root`, only the modules named
/// in `only` when it is given, and `root` itself is then not read.
fn tree(root: &Path, only: Option<&[&str]>) -> Vec<(PathBuf, String)> {
    let mut out = Vec::new();
    let mut todo = vec![(root.to_path_buf(), true)];
    while let Some((f, top)) = todo.pop() {
        let text = fs::read_to_string(&f).unwrap_or_else(|e| panic!("{}: {e}", f.display()));
        let lines = lex(&text);
        let (live, _) = live(&lines);
        let raw: Vec<&str> = text.split('\n').collect();
        for (k, l) in lines.iter().enumerate() {
            if !live[k] {
                continue;
            }
            let code = l.code.trim();
            if code.starts_with("#[path") {
                panic!(
                    "{}:{}: a module at a path of its own, which this test does not follow",
                    f.display(),
                    k + 1
                );
            }
            if let Some(name) = declared_mod(code) {
                if top && only.is_some_and(|o| !o.contains(&name)) {
                    continue;
                }
                let d = module_dir(&f);
                let file = d.join(format!("{name}.rs"));
                let file = if file.exists() {
                    file
                } else {
                    d.join(name).join("mod.rs")
                };
                todo.push((file, false));
            }
            if code.contains("include!(") {
                let inc = raw[k]
                    .split('"')
                    .nth(1)
                    .expect("include! of a literal path");
                todo.push((f.parent().expect("a directory").join(inc), false));
            }
        }
        if !(top && only.is_some()) {
            out.push((f, text));
        }
    }
    out
}

/// The files a built executable runs, as the head comment lists them.
fn runtime_files() -> Vec<(PathBuf, String)> {
    let crates = steps_dir().join("../../crates");
    let mut files = tree(&crates.join("zed-rt/src/lib.rs"), None);
    files.extend(tree(
        &crates.join("zed-native/src/lib.rs"),
        Some(&["exe", "legal", "tables", "outcome", "hooks", "bug"]),
    ));
    files
}

#[test]
fn every_runtime_panic_site_says_why_it_cannot_fire() {
    let files = runtime_files();
    let names: Vec<String> = files.iter().map(|(f, _)| f.display().to_string()).collect();
    for want in [
        "zed-rt/src/heap.rs",
        "zed-rt/src/stack/growing.rs",
        "zed-native/src/hooks.rs",
    ] {
        assert!(
            names.iter().any(|n| n.ends_with(want)),
            "the module tree read lacks {want}: {names:?}"
        );
    }
    assert!(
        !names
            .iter()
            .any(|n| n.ends_with("codegen.rs") || n.ends_with("completeness.rs")),
        "the module tree read has a compiler or test file: {names:?}"
    );
    let mut problems = Vec::new();
    let mut total = 0;
    for (f, text) in &files {
        let (count, faults, _) = check(text);
        total += count;
        let f = f.display();
        for (line, kinds) in &faults.bare {
            problems.push(format!(
                "{f}:{line}: {} with no `{MARKER} <why>` before it or at its end. Repair: say \
                 there why its condition always holds, or return an error where it can fail",
                kinds.join(", ")
            ));
        }
        for line in &faults.stale {
            problems.push(format!(
                "{f}:{line}: `{MARKER}` covers no site. Repair: remove it, or put it before \
                 its site"
            ));
        }
        for line in &faults.empty {
            problems.push(format!(
                "{f}:{line}: `{MARKER}` gives no reason. Repair: give one"
            ));
        }
    }
    eprintln!("{total} panic sites in {} files", files.len());
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}

#[test]
fn a_site_with_no_comment_fails() {
    let text = "fn f(v: &[u8], i: usize) -> u8 {
    // Cannot panic: the caller checks `i + 1 < v.len()`.
    let a = v[i];

    let b = v[i + 1];
    a + b
}
";
    let (count, faults, _) = check(text);
    assert_eq!(count, 2);
    assert_eq!(
        faults,
        Faults {
            bare: vec![(5, vec!["index"])],
            ..Faults::default()
        }
    );
}

/// The red run on real code: crates/zed-rt/src/line.rs with the comment of one site taken
/// out fails on that site alone, and passes as it is.
#[test]
fn a_runtime_file_with_one_comment_taken_out_fails_on_that_site() {
    let path = steps_dir().join("../../crates/zed-rt/src/line.rs");
    let text = fs::read_to_string(&path).expect("line.rs is readable");
    assert_eq!(check(&text).1, Faults::default());
    let at = text.find(MARKER).expect("line.rs has a reason");
    let end = at + text[at..].find('\n').expect("a line break");
    let start = text[..at].rfind('\n').expect("a line before") + 1;
    let cut = format!("{}{}", &text[..start], &text[end + 1..]);
    let site = 1 + text[..start].matches('\n').count();
    let (_, faults, _) = check(&cut);
    assert_eq!(faults.bare.len(), 1, "{faults:?}");
    assert_eq!(faults.bare[0].0, site, "{faults:?}");
    assert!(
        faults.stale.is_empty() && faults.empty.is_empty(),
        "{faults:?}"
    );
}

#[test]
fn literals_comments_tests_and_the_whole_slice_are_not_sites() {
    let text = r##"fn f<'a>(x: &'a [u8], v: Vec<[u8; 2]>) -> &'a [u8] {
    let s = "a[0].unwrap() panic!()";
    let r = r#"x["y"].expect("z")"#;
    let c = ('[', '\'', b']');
    /* x[0] /* nested.unwrap() */ y[1] */
    let w = vec![0; 2];
    let all = &x[..];
    let s2 = "line one
        x[1] in the string";
    // Cannot panic: a reason that covers no site.

    x // x[0] in a comment
}

#[cfg(test)]
mod tests {
    fn g(v: &[u8]) -> u8 {
        v[0] + Some(1).unwrap()
    }
}

#[cfg(test)]
mod completeness;

fn h(v: &[u8]) -> u8 {
    v[0] // Cannot panic: a reason at the end of its line.
}

fn k(v: &[u8]) -> u8 {
    // Cannot panic:
    v[1]
}
"##;
    let (count, faults, tests) = check(text);
    assert_eq!(count, 2);
    assert_eq!(
        faults,
        Faults {
            bare: Vec::new(),
            stale: vec![10],
            empty: vec![30],
        }
    );
    assert_eq!(tests, ["completeness"]);
    assert_eq!(declared_mod("pub(crate) mod tests;"), Some("tests"));
    assert_eq!(sites("std::panic!(\"x\")"), ["panic"]);
    assert_eq!(
        sites("let y = f(x)[0].0.expect(\"x\");"),
        ["expect", "index"]
    );
}
